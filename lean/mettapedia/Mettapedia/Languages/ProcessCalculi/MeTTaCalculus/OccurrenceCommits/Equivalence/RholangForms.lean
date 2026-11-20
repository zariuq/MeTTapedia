import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.AgentLaws
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits
import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.Enum

/-!
# Settled Rholang receive forms over `transform`

Rholang has three kinds of receipt and a choice among receives:

* linear `for (p₁ <- c₁ & … & pₙ <- cₙ) P`: consumes the receiver and one message on each channel;
* repeated `for (p₁ <= c₁ & …) P` (and `contract`): consumes the messages and stays;
* peek `for (p₁ <<- c₁ & …) P`: consumes the receiver and leaves the messages;
* `select { p₁ <- a & q₁ <- b => P ; r <- c => Q }`: consumes the select and, for one arm, one
  message on each channel of the arm's linear join.

The settled surface rules (`RhoRule`) describe messages and receivers whose
channels and continuations have already been prepared. Their definitions
over `transform` are given by `encode`:

* linear: `await (transform (, (take p₁ @ c₁) …) P)`;
* repeated: `whenever (transform (, (take p₁ @ c₁) …) P)`;
* peek: `await (transform (, (read p₁ @ c₁) …) P)`;
* select: `await (choose (transform (, (take p₁ @ a) (take q₁ @ b)) P) …)`, one transform per arm,
  taking every bind of the arm (`armTr`).

A select whose arms bind one channel each is the fragment of arms with no further bind
(`oneBind`, `select_oneBind`, `armTr_oneBind`). `Equivalence.RholangSelectJoins` has the controls
that tell a join arm from its first bind.

## The theorem

* **The rules correspond exactly** (`rholang_correspond`): every Rholang reduction rule is, label by
  label, a rule the transform definitions generate, and every generated rule whose labels are all
  encodings of Rholang processes is the encoding of a Rholang rule.
* **So bisimilarity is preserved and reflected** (`bisimilar_rholang_iff`): two Rholang soups are
  bisimilar over borrowed contexts exactly when their encodings are, relative to environments that
  are themselves Rholang soups. The transform language has more contexts (none readers,
  predicate queries, mixed `read`/`take` receivers); relative to those, the encodings may be told apart where
  Rholang's own contexts cannot, so this is full abstraction for Rholang's environments, not for
  all of MeTTa's.

The settled model does not represent intermediate interpreter states. In
particular, restoring a message after a runtime peek is not an atomic
physical read. The prepared scan below separately models which packets the
Rust store finds, before any messages are removed.

The general tool is a transport of bisimilarity along an injective relabelling between positive rule
sets that correspond (`Correspond`, `bisimilar_map_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u v w

/-! ## Transport along a relabelling -/

section Transport

variable {R : Type u} {R' : Type v} [DecidableEq R] [DecidableEq R'] (f : R → R')

/-- A positive rule, relabelled. -/
def Rule.mapPos (ρ : Rule R) : Rule R' := ⟨ρ.take.map f, ρ.keep.map f, ρ.make.map f, fun _ => false⟩

/-- Labels in the image of the relabelling. -/
def Image (y : R') : Prop := ∃ x, f x = y

/-- **Corresponding rule sets**: positive, every rule relabels to a rule, and every rule over
relabelled labels is a relabelled rule. -/
structure Correspond (Γ : Rule R → Prop) (Γ' : Rule R' → Prop) : Prop where
  positive : PositiveRules Γ
  forward : ∀ ρ, Γ ρ → Γ' (ρ.mapPos f)
  backward : ∀ ρ', Γ' ρ' → (∀ y ∈ ρ'.redex, Image f y) → ∃ ρ, Γ ρ ∧ ρ' = ρ.mapPos f

variable {f}

theorem map_sub_of_injective (hf : Function.Injective f) (A B : Multiset R) :
    (A - B).map f = A.map f - B.map f := by
  ext y
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    simp only [Multiset.count_sub, Multiset.count_map_eq_count' f _ hf]
  · have zero : ∀ M : Multiset R, Multiset.count y (M.map f) = 0 := fun M =>
      Multiset.count_eq_zero.mpr fun member => by
        obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp member
        exact hy ⟨x, rfl⟩
    rw [Multiset.count_sub, zero, zero, zero]

omit [DecidableEq R] [DecidableEq R'] in
theorem mapPos_redex (ρ : Rule R) : (ρ.mapPos f).redex = ρ.redex.map f := by
  simp [Rule.mapPos, Rule.redex, Multiset.map_add]

theorem mapPos_result (hf : Function.Injective f) (ρ : Rule R) (M : Multiset R) :
    (ρ.mapPos f).result (M.map f) = (ρ.result M).map f := by
  simp [Rule.mapPos, Rule.result, Multiset.map_add, map_sub_of_injective hf]

/-- A positive step, relabelled. -/
theorem Rule.Step.map (hf : Function.Injective f) {ρ : Rule R}
    {M M' J : Multiset R} {F : R → Bool} (step : ρ.Step M ⟨J, F⟩ M') :
    (ρ.mapPos f).Step (M.map f) ⟨J.map f, fun _ => false⟩ (M'.map f) := by
  obtain ⟨hJ, -, -, hM⟩ := step
  simp only at hJ hM
  subst hJ hM
  refine ⟨by rw [mapPos_redex, map_sub_of_injective hf], rfl, fun _ _ => rfl, ?_⟩
  simp only
  rw [← Multiset.map_add, mapPos_result hf]

/-- A relabelled step from a relabelled bag is the relabelling of a step. -/
theorem Rule.Step.unmap (hf : Function.Injective f) {ρ : Rule R} (positive : ρ.Positive)
    {M : Multiset R} {J' X' : Multiset R'} {G : R' → Bool}
    (step : (ρ.mapPos f).Step (M.map f) ⟨J', G⟩ X') :
    ∃ J X, J' = J.map f ∧ X' = X.map f ∧ ρ.Step M ⟨J, ρ.closed⟩ X := by
  obtain ⟨hJ, -, -, hX⟩ := step
  simp only at hJ hX
  refine ⟨ρ.redex - M, ρ.result (M + (ρ.redex - M)), ?_, ?_, ⟨rfl, rfl, fun x _ => positive x, rfl⟩⟩
  · rw [hJ, mapPos_redex, map_sub_of_injective hf]
  · rw [hX, hJ, mapPos_redex, ← map_sub_of_injective hf, ← Multiset.map_add, mapPos_result hf]

variable {Γ : Rule R → Prop} {Γ' : Rule R' → Prop} {ι : Type w} {obs : ι → R → Prop}

/-- Barbs read through the relabelling. -/
def mapObs (f : R → R') (obs : ι → R → Prop) : ι → R' → Prop := fun i y => ∃ x, f x = y ∧ obs i x

omit [DecidableEq R] [DecidableEq R'] in
theorem barb_map_iff (hf : Function.Injective f) {region : R → Prop} {M : Multiset R} :
    Barb (fun y => ∃ x, f x = y ∧ region x) (M.map f) ↔ Barb region M := by
  constructor
  · rintro ⟨y, member, x, rfl, h⟩
    obtain ⟨x', inM, eq⟩ := Multiset.mem_map.mp member
    exact ⟨x', inM, hf eq ▸ h⟩
  · rintro ⟨x, member, h⟩
    exact ⟨f x, Multiset.mem_map_of_mem f member, x, rfl, h⟩

omit [DecidableEq R] [DecidableEq R'] in
/-- A bag of image labels is the relabelling of a bag. -/
theorem exists_map_of_image {J' : Multiset R'} (image : ∀ y ∈ J', Image f y) :
    ∃ J : Multiset R, J' = J.map f := by
  classical
  by_cases hR : Nonempty R
  · refine ⟨J'.map (Function.invFun f), ?_⟩
    rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id J']
    refine Multiset.map_congr rfl fun y member => ?_
    exact (Function.invFun_eq (image y member)).symm
  · refine ⟨0, ?_⟩
    rw [Multiset.map_zero, Multiset.eq_zero_iff_forall_notMem]
    intro y member
    obtain ⟨x, -⟩ := image y member
    exact hR ⟨x⟩

/-- A step of a relabelled bag with an image label is the relabelling of a step. -/
theorem BStep.unmap (corr : Correspond f Γ Γ') (hf : Function.Injective f) {M : Multiset R}
    {J' X' : Multiset R'} {G : R' → Bool} (image : ∀ y ∈ J', Image f y)
    (step : BStep Γ' (M.map f) ⟨J', G⟩ X') :
    ∃ J X F, J' = J.map f ∧ X' = X.map f ∧ BStep Γ M ⟨J, F⟩ X := by
  obtain ⟨ρ', member, stepρ⟩ := step
  have redexImage : ∀ y ∈ ρ'.redex, Image f y := by
    obtain ⟨hJ, -, -, -⟩ := stepρ
    simp only at hJ
    intro y inRedex
    have : ρ'.redex ≤ M.map f + J' := by rw [hJ]; exact le_add_label' _ _
    rcases Multiset.mem_add.mp (Multiset.mem_of_le this inRedex) with h | h
    · obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp h; exact ⟨x, rfl⟩
    · exact image y h
  obtain ⟨ρ, inΓ, rfl⟩ := corr.backward ρ' member redexImage
  obtain ⟨J, X, rfl, rfl, stepM⟩ := stepρ.unmap hf (corr.positive ρ inΓ)
  exact ⟨J, X, ρ.closed, rfl, rfl, ρ, inΓ, stepM⟩

/-- A step, relabelled. -/
theorem BStep.map (corr : Correspond f Γ Γ') (hf : Function.Injective f) {M M' J : Multiset R}
    {F : R → Bool} (step : BStep Γ M ⟨J, F⟩ M') :
    BStep Γ' (M.map f) ⟨J.map f, fun _ => false⟩ (M'.map f) := by
  obtain ⟨ρ, member, stepρ⟩ := step
  exact ⟨ρ.mapPos f, corr.forward ρ member, stepρ.map hf⟩

/-- **Bisimilarity transports along corresponding rule sets**: two bags are bisimilar (every label
admissible) exactly when their relabellings are bisimilar relative to relabelled environments. -/
theorem bisimilar_map_iff (corr : Correspond f Γ Γ') (hf : Function.Injective f) {M N : Multiset R} :
    Bisimilar Γ (fun _ => True) obs M N ↔ Bisimilar Γ' (Image f) (mapObs f obs) (M.map f) (N.map f) := by
  constructor
  · rintro ⟨B, bisim, related⟩
    refine ⟨fun X Y => ∃ M N, B M N ∧ X = M.map f ∧ Y = N.map f, ⟨?_, ?_, ?_⟩, ⟨M, N, related, rfl, rfl⟩⟩
    · rintro X Y ⟨M, N, rel, rfl, rfl⟩
      exact ⟨N, M, bisim.symm rel, rfl, rfl⟩
    · rintro X Y ⟨M, N, rel, rfl, rfl⟩ i shows
      exact (barb_map_iff hf).mpr (bisim.barb rel i ((barb_map_iff hf).mp shows))
    · rintro X Y ⟨M, N, rel, rfl, rfl⟩ J' F' X' adm step
      obtain ⟨J, X₀, F, rfl, rfl, stepM⟩ := step.unmap corr hf adm
      obtain ⟨G, N', -, answer, rel'⟩ := bisim.step rel (fun _ _ => trivial) stepM
      refine ⟨fun _ => false, N'.map f, weaker_none _ _, ?_, ⟨X₀, N', rel', rfl, rfl⟩⟩
      have := answer.map corr hf
      simpa [Multiset.map_add] using this
  · rintro ⟨B, bisim, related⟩
    refine ⟨fun M N => B (M.map f) (N.map f), ⟨fun _ _ h => bisim.symm h, ?_, ?_⟩, related⟩
    · intro M N rel i shows
      exact (barb_map_iff hf).mp (bisim.barb rel i ((barb_map_iff hf).mpr shows))
    · intro M N rel J F M' _ step
      obtain ⟨G', Y, -, answer, rel'⟩ := bisim.step rel
        (fun y member => by obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp member; exact ⟨x, rfl⟩)
        (step.map corr hf)
      rw [← Multiset.map_add] at answer
      obtain ⟨J₀, N', F', hJ₀, rfl, stepN⟩ := answer.unmap corr hf (by simp)
      have hJ0 : J₀ = 0 := by
        have := congrArg Multiset.card hJ₀
        simp at this
        exact Multiset.card_eq_zero.mp this.symm
      subst hJ0
      refine ⟨F', N', ?_, stepN, rel'⟩
      intro x _ h
      obtain ⟨ρ, member, ⟨-, hF, -, -⟩⟩ := stepN
      simp only at hF
      rw [hF, corr.positive ρ member x] at h
      exact absurd h (by decide)

end Transport

/-! ## Rholang's receive forms -/

namespace Rholang

open Agents

/-- The receipt kinds: linear `<-`, repeated `<=`, peek `<<-`. -/
inductive Kind where
  | linear
  | repeated
  | peek
  deriving DecidableEq, Repr

/-- An arm of a select: a linear receipt (first bind, further binds) and its continuation. -/
abbrev Arm (Ch : Type u) (Pat : Type v) (K : Type w) := (Ch × Pat) × List (Ch × Pat) × K

/-- Rholang's receivers: a receipt of one kind over at least one bind, or a select over arms that
are linear joins. Continuations are named process abstractions. -/
inductive Recv (Ch : Type u) (Pat : Type v) (K : Type w) where
  | receipt (kind : Kind) (first : Ch × Pat) (rest : List (Ch × Pat)) (k : K)
  | select (arms : List (Arm Ch Pat K))
  deriving DecidableEq

/-- Rholang's soup: messages and receivers. -/
inductive RhoLbl (Ch : Type u) (Val : Type u) (Pat : Type v) (K : Type w) where
  | msg (c : Ch) (x : Val)
  | recv (r : Recv Ch Pat K)
  deriving DecidableEq

variable {Ch Val : Type u} {Pat : Type v} {K : Type w}
variable (sat : Pat → Val → Prop)

/-- The messages a receive consumes or reads, bind by bind. -/
def msgs {L : Type*} (mk : Ch → Val → L) (binds : List (Ch × Pat)) (vals : List Val) : Multiset L :=
  ((binds.zip vals).map fun bv => mk bv.1.1 bv.2 : List L)

/-- Values that the binds' patterns accept, one per bind. -/
def Accepts (binds : List (Ch × Pat)) (vals : List Val) : Prop :=
  List.Forall₂ (fun b x => sat b.2 x) binds vals

variable (body : K → List Val → Multiset (RhoLbl Ch Val Pat K))

/-- **Rholang's reduction rules**, as Rholang states them. -/
inductive RhoRule : Rule (RhoLbl Ch Val Pat K) → Prop
  | linear {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      Accepts sat (b :: bs) vals →
      RhoRule ⟨.recv (.receipt .linear b bs k) ::ₘ msgs .msg (b :: bs) vals, 0, body k vals, fun _ => false⟩
  | repeated {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      Accepts sat (b :: bs) vals →
      RhoRule ⟨msgs .msg (b :: bs) vals, {.recv (.receipt .repeated b bs k)}, body k vals, fun _ => false⟩
  | peek {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      Accepts sat (b :: bs) vals →
      RhoRule ⟨{.recv (.receipt .peek b bs k)}, msgs .msg (b :: bs) vals, body k vals, fun _ => false⟩
  | select {arms : List (Arm Ch Pat K)} {b : Ch × Pat} {bs : List (Ch × Pat)} {k : K} {vals : List Val} :
      (b, bs, k) ∈ arms → Accepts sat (b :: bs) vals →
      RhoRule ⟨.recv (.select arms) ::ₘ msgs .msg (b :: bs) vals, 0, body k vals, fun _ => false⟩

/-! ### The transform side -/

/-- How a source uses what it matches. -/
inductive Mode where
  | take
  | read
  deriving DecidableEq, Repr

/-- A source: a channel, a mode, a pattern. -/
structure Src (Ch : Type u) (Pat : Type v) where
  ch : Ch
  mode : Mode
  pat : Pat
  deriving DecidableEq

/-- A transform: its sources and the named template. -/
structure Tr (Ch : Type u) (Pat : Type v) (K : Type w) where
  sources : List (Src Ch Pat)
  k : K
  deriving DecidableEq

/-- Labels of the transform side: messages as data, and parked processes. -/
abbrev TLbl (Ch Val : Type u) (Pat : Type v) (K : Type w) := Agents.Lbl (Ch × Val) (Tr Ch Pat K)

/-- The messages of the sources of one mode. -/
def modeMsgs (mode : Mode) (sources : List (Src Ch Pat)) (vals : List Val) : Multiset (TLbl Ch Val Pat K) :=
  (((sources.zip vals).filter fun sv => sv.1.mode = mode).map fun sv => Lbl.data (sv.1.ch, sv.2) :
    List (TLbl Ch Val Pat K))

variable (tbody : K → List Val → Multiset (TLbl Ch Val Pat K))

/-- **The rows of a transform**: values accepted by its sources' patterns; the take sources' messages
are taken, the read sources' messages kept, the template made. -/
def trRows (t : Tr Ch Pat K) (r : Rule (TLbl Ch Val Pat K)) : Prop :=
  ∃ vals, List.Forall₂ (fun s x => sat s.pat x) t.sources vals ∧
    r = ⟨modeMsgs .take t.sources vals, modeMsgs .read t.sources vals, tbody t.k vals, fun _ => false⟩

/-- A list of binds as sources of one mode. -/
def asSources (mode : Mode) (binds : List (Ch × Pat)) : List (Src Ch Pat) :=
  binds.map fun cp => ⟨cp.1, mode, cp.2⟩

/-- The transform of an arm: every bind of its receipt taken, in one firing. -/
def armTr (a : Arm Ch Pat K) : Tr Ch Pat K := ⟨asSources .take (a.1 :: a.2.1), a.2.2⟩

/-- **The definitions**: each Rholang receiver as a parked transform; a select as one parked choice
over the transforms of its arms. -/
def encodeRecv : Recv Ch Pat K → Agent (Tr Ch Pat K)
  | .receipt .linear b bs k => .await ⟨asSources .take (b :: bs), k⟩
  | .receipt .repeated b bs k => .whenever ⟨asSources .take (b :: bs), k⟩
  | .receipt .peek b bs k => .await ⟨asSources .read (b :: bs), k⟩
  | .select arms => .choose (arms.map armTr)

/-- The encoding of the soup. -/
def encode : RhoLbl Ch Val Pat K → TLbl Ch Val Pat K
  | .msg c x => .data (c, x)
  | .recv r => .agent (encodeRecv r)

/-! ### One-bind arms -/

/-- An arm that binds one channel: a join arm with no further bind. -/
def oneBind (a : Ch × Pat × K) : Arm Ch Pat K := ((a.1, a.2.1), [], a.2.2)

/-- **A one-bind arm's transform takes its one bind.** -/
theorem armTr_oneBind (a : Ch × Pat × K) :
    armTr (oneBind a) = ⟨[⟨a.1, .take, a.2.1⟩], a.2.2⟩ := rfl

variable {sat body} in
/-- **A select over one-bind arms consumes the select and one message**, as Rholang's one-bind
`select` does. -/
theorem select_oneBind {arms : List (Ch × Pat × K)} {c : Ch} {p : Pat} {k : K} {x : Val}
    (member : (c, p, k) ∈ arms) (accepts : sat p x) :
    RhoRule sat body ⟨{.recv (.select (arms.map oneBind)), .msg c x}, 0, body k [x], fun _ => false⟩ := by
  have := RhoRule.select (sat := sat) (body := body) (arms := arms.map oneBind) (b := (c, p))
    (bs := []) (k := k) (vals := [x]) (List.mem_map_of_mem (f := oneBind) member)
    (List.Forall₂.cons accepts List.Forall₂.nil)
  simpa [msgs] using this

/-! ### The correspondence -/

section Correspondence

variable {sat} {body}

theorem asSources_injective (mode : Mode) : Function.Injective (asSources (Ch := Ch) (Pat := Pat) mode) := by
  intro a b h
  refine List.map_injective_iff.mpr ?_ h
  intro x y hxy
  simp only [Src.mk.injEq] at hxy
  exact Prod.ext hxy.1 hxy.2.2

theorem accepts_iff (mode : Mode) (binds : List (Ch × Pat)) (vals : List Val) :
    List.Forall₂ (fun s x => sat s.pat x) (asSources mode binds) vals ↔ Accepts sat binds vals := by
  unfold asSources Accepts
  rw [List.forall₂_map_left_iff]

theorem modeMsgs_same (mode : Mode) (binds : List (Ch × Pat)) (vals : List Val) :
    modeMsgs (K := K) mode (asSources mode binds) vals = (msgs RhoLbl.msg binds vals).map (encode (Pat := Pat) (K := K)) := by
  unfold modeMsgs msgs asSources
  rw [List.zip_map_left, List.filter_map]
  have : ((binds.zip vals).filter ((fun sv : Src Ch Pat × Val => decide (sv.1.mode = mode)) ∘
      Prod.map (fun cp : Ch × Pat => (⟨cp.1, mode, cp.2⟩ : Src Ch Pat)) id)) = binds.zip vals :=
    List.filter_eq_self.mpr fun _ _ => by simp
  rw [this, Multiset.map_coe, List.map_map, List.map_map]
  rfl

theorem modeMsgs_other {mode mode' : Mode} (ne : mode' ≠ mode) (binds : List (Ch × Pat)) (vals : List Val) :
    modeMsgs (Val := Val) (K := K) mode' (asSources mode binds) vals = 0 := by
  unfold modeMsgs asSources
  rw [List.zip_map_left, List.filter_map]
  have : ((binds.zip vals).filter ((fun sv : Src Ch Pat × Val => decide (sv.1.mode = mode')) ∘
      Prod.map (fun cp : Ch × Pat => (⟨cp.1, mode, cp.2⟩ : Src Ch Pat)) id)) = [] :=
    List.filter_eq_nil_iff.mpr fun _ _ => by simp [Ne.symm ne]
  rw [this]
  rfl

theorem armTr_injective : Function.Injective (armTr (Ch := Ch) (Pat := Pat) (K := K)) := by
  rintro ⟨b, bs, k⟩ ⟨b', bs', k'⟩ h
  simp only [armTr, Tr.mk.injEq] at h
  obtain ⟨hs, rfl⟩ := h
  have := asSources_injective .take hs
  simp only [List.cons.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  rfl

theorem encodeRecv_injective : Function.Injective (encodeRecv (Ch := Ch) (Pat := Pat) (K := K)) := by
  intro r r' h
  cases r with
  | receipt kind b bs k =>
      cases r' with
      | receipt kind' b' bs' k' =>
          cases kind <;> cases kind' <;> simp only [encodeRecv, Agent.await.injEq, Agent.whenever.injEq,
            reduceCtorEq, Tr.mk.injEq] at h <;>
            first
            | (obtain ⟨hs, rfl⟩ := h
               have := asSources_injective _ hs
               simp only [List.cons.injEq] at this
               obtain ⟨rfl, rfl⟩ := this
               rfl)
            | (obtain ⟨hs, -⟩ := h
               simp only [asSources, List.map_cons, List.cons.injEq, Src.mk.injEq] at hs
               exact absurd hs.1.2.1 (by decide))
      | select arms => cases kind <;> simp [encodeRecv] at h
  | select arms =>
      cases r' with
      | receipt kind' b' bs' k' => cases kind' <;> simp [encodeRecv] at h
      | select arms' =>
          simp only [encodeRecv, Agent.choose.injEq] at h
          rw [List.map_injective_iff.mpr armTr_injective h]

theorem encode_injective : Function.Injective (encode (Ch := Ch) (Val := Val) (Pat := Pat) (K := K)) := by
  intro x y h
  cases x with
  | msg c v =>
      cases y with
      | msg c' v' => simp only [encode, Lbl.data.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]
      | recv r => simp [encode] at h
  | recv r =>
      cases y with
      | msg c' v' => simp [encode] at h
      | recv r' =>
          simp only [encode, Lbl.agent.injEq] at h
          rw [encodeRecv_injective h]

theorem rhoRule_positive : PositiveRules (RhoRule (Ch := Ch) (Val := Val) (Pat := Pat) (K := K) sat body) := by
  intro ρ h x
  cases h <;> rfl

/-- **Rholang's rules and the transform definitions correspond exactly.** -/
theorem rholang_correspond [DecidableEq Ch] [DecidableEq Val] [DecidableEq Pat] [DecidableEq K] :
    Correspond (encode (Ch := Ch) (Val := Val) (Pat := Pat) (K := K)) (RhoRule sat body)
      (Fires (trRows sat fun k vals => (body k vals).map encode)) := by
  refine ⟨rhoRule_positive, ?_, ?_⟩
  · intro ρ h
    cases h with
    | @linear b bs k vals acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode)
            ⟨asSources .take (b :: bs), k⟩
            ⟨modeMsgs .take (asSources .take (b :: bs)) vals, modeMsgs .read (asSources .take (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .take _ _).mpr acc, rfl⟩
        have := Fires.await row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
    | @repeated b bs k vals acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode)
            ⟨asSources .take (b :: bs), k⟩
            ⟨modeMsgs .take (asSources .take (b :: bs)) vals, modeMsgs .read (asSources .take (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .take _ _).mpr acc, rfl⟩
        have := Fires.whenever row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
    | @peek b bs k vals acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode)
            ⟨asSources .read (b :: bs), k⟩
            ⟨modeMsgs .take (asSources .read (b :: bs)) vals, modeMsgs .read (asSources .read (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .read _ _).mpr acc, rfl⟩
        have := Fires.await row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
    | @select arms b bs k vals member acc =>
        have row : trRows sat (fun k vals => (body k vals).map encode) (armTr (b, bs, k))
            ⟨modeMsgs .take (asSources .take (b :: bs)) vals, modeMsgs .read (asSources .take (b :: bs)) vals,
              (body k vals).map encode, fun _ => false⟩ :=
          ⟨vals, (accepts_iff .take _ _).mpr acc, rfl⟩
        have := Fires.choose (ts := arms.map armTr) (List.mem_map_of_mem member) row
        rw [modeMsgs_same, modeMsgs_other (by decide)] at this
        convert this using 1
        simp [Rule.mapPos, encode, encodeRecv]
  · intro ρ' h image
    cases h with
    | @await t r row =>
        obtain ⟨vals, acc, rfl⟩ := row
        obtain ⟨x, hx⟩ := image (Lbl.agent (.await t)) (by simp [Rule.redex])
        cases x with
        | msg c v => simp [encode] at hx
        | recv rr =>
            cases rr with
            | select arms => simp [encode, encodeRecv] at hx
            | receipt kind b bs k =>
                cases kind with
                | repeated => simp [encode, encodeRecv] at hx
                | linear =>
                    simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.await.injEq] at hx
                    subst hx
                    refine ⟨_, RhoRule.linear (b := b) (bs := bs) (k := k) ((accepts_iff .take _ _).mp acc), ?_⟩
                    simp only [Rule.mapPos]
                    rw [modeMsgs_same, modeMsgs_other (by decide)]
                    simp [encode, encodeRecv]
                | peek =>
                    simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.await.injEq] at hx
                    subst hx
                    refine ⟨_, RhoRule.peek (b := b) (bs := bs) (k := k) ((accepts_iff .read _ _).mp acc), ?_⟩
                    simp only [Rule.mapPos]
                    rw [modeMsgs_same, modeMsgs_other (by decide)]
                    simp [encode, encodeRecv]
    | @whenever t r row =>
        obtain ⟨vals, acc, rfl⟩ := row
        obtain ⟨x, hx⟩ := image (Lbl.agent (.whenever t)) (by simp [Rule.redex])
        cases x with
        | msg c v => simp [encode] at hx
        | recv rr =>
            cases rr with
            | select arms => simp [encode, encodeRecv] at hx
            | receipt kind b bs k =>
                cases kind with
                | linear => simp [encode, encodeRecv] at hx
                | peek => simp [encode, encodeRecv] at hx
                | repeated =>
                    simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.whenever.injEq] at hx
                    subst hx
                    refine ⟨_, RhoRule.repeated (b := b) (bs := bs) (k := k) ((accepts_iff .take _ _).mp acc), ?_⟩
                    simp only [Rule.mapPos]
                    rw [modeMsgs_same, modeMsgs_other (by decide)]
                    simp [encode, encodeRecv]
    | @choose ts t r tmem row =>
        obtain ⟨vals, acc, rfl⟩ := row
        obtain ⟨x, hx⟩ := image (Lbl.agent (.choose ts)) (by simp [Rule.redex])
        cases x with
        | msg c v => simp [encode] at hx
        | recv rr =>
            cases rr with
            | receipt kind b bs k => cases kind <;> simp [encode, encodeRecv] at hx
            | select arms =>
                simp only [encode, encodeRecv, Lbl.agent.injEq, Agent.choose.injEq] at hx
                subst hx
                obtain ⟨⟨b, bs, k⟩, armMem, rfl⟩ := List.mem_map.mp tmem
                refine ⟨_, RhoRule.select armMem ((accepts_iff .take _ _).mp acc), ?_⟩
                simp only [Rule.mapPos, armTr]
                rw [modeMsgs_same, modeMsgs_other (by decide)]
                simp [encode, encodeRecv]

/-- **Rholang soups are bisimilar exactly when their encodings are**, relative to environments that
are themselves Rholang soups. -/
theorem bisimilar_rholang_iff [DecidableEq Ch] [DecidableEq Val] [DecidableEq Pat] [DecidableEq K]
    {ι : Type*} {obs : ι → RhoLbl Ch Val Pat K → Prop}
    {M N : Multiset (RhoLbl Ch Val Pat K)} :
    Bisimilar (RhoRule sat body) (fun _ => True) obs M N ↔
      Bisimilar (Fires (trRows sat fun k vals => (body k vals).map encode)) (Image encode)
        (mapObs encode obs) (M.map encode) (N.map encode) :=
  bisimilar_map_iff rholang_correspond encode_injective

end Correspondence

namespace Prepared

/-!
## The ordered packet at a Rust receive

The normalizer checks channel expressions before evaluation. The store sees
their resolved channels, an ordered candidate vector per channel, and an
independent matcher for each bind. Its private scan visits the binds from
last to first, updates only their local candidate caches, and restores bind
order in the returned packet. A failed scan makes no delivery packet.

The matched bindings and the untouched datum are distinct fields: dispatch
uses the former, while a later peek repost uses the latter.
-/

variable {Ch : Type u} {Pat : Type v} {Val : Type u} {Arg : Type w}

/-- One candidate row. The incoming produce is offered with index `-1`
before it has been inserted; all stored candidates have a store index. -/
structure Datum (Val : Type u) where
  raw : Val
  index : Int
  persistent : Bool
  deriving DecidableEq

structure Match (Val : Type u) (Arg : Type w) where
  datum : Datum Val
  captures : List Arg
  deriving DecidableEq

variable (capture : Pat → Val → Option (List Arg))

/-- The first match in one candidate vector. A linear datum is removed from
the cache. The persistent case keeps the successful suffix, as the Rust
worker does; neither branch mutates the tuplespace here. -/
def pick (pattern : Pat) : List (Datum Val) → Option (Match Val Arg × List (Datum Val))
  | [] => none
  | row :: rest =>
      match capture pattern row.raw with
      | some args => some (⟨row, args⟩, if row.persistent then row :: rest else rest)
      | none => (pick pattern rest).map fun r =>
          (r.1, if r.1.datum.persistent then r.2 else row :: r.2)

theorem pick_sound (pattern : Pat) :
    ∀ {rows : List (Datum Val)} {selected : Match Val Arg} {rest : List (Datum Val)},
      pick capture pattern rows = some (selected, rest) →
      selected.datum ∈ rows ∧ capture pattern selected.datum.raw = some selected.captures ∧ rest ⊆ rows
  | [], _, _, computed => by simp [pick] at computed
  | row :: rows, selected, rest, computed => by
      cases checked : capture pattern row.raw with
      | some args =>
          simp only [pick, checked, Option.some.injEq, Prod.mk.injEq] at computed
          obtain ⟨rfl, rfl⟩ := computed
          refine ⟨List.mem_cons_self, checked, ?_⟩
          split
          · exact fun _ member => member
          · exact fun _ member => List.mem_cons_of_mem _ member
      | none =>
          simp only [pick, checked, Option.map_eq_some_iff] at computed
          obtain ⟨⟨chosen, tail⟩, later, equal⟩ := computed
          simp only [Prod.mk.injEq] at equal
          obtain ⟨rfl, rfl⟩ := equal
          obtain ⟨present, matched, sub⟩ := pick_sound pattern later
          refine ⟨List.mem_cons_of_mem _ present, matched, ?_⟩
          split
          · exact fun _ member => List.mem_cons_of_mem _ (sub member)
          · intro value member
            exact (List.mem_cons.mp member).elim
              (fun equal => equal ▸ List.mem_cons_self) (fun later => List.mem_cons_of_mem _ (sub later))

theorem pick_none_iff (pattern : Pat) (rows : List (Datum Val)) :
    pick capture pattern rows = none ↔ ∀ row ∈ rows, capture pattern row.raw = none := by
  induction rows with
  | nil => simp [pick]
  | cons row rows earlier =>
      cases checked : capture pattern row.raw <;>
        simp [pick, checked, earlier]

theorem pick_isSome_iff (pattern : Pat) (rows : List (Datum Val)) :
    (pick capture pattern rows).isSome ↔
      ∃ datum ∈ rows, ∃ captures, capture pattern datum.raw = some captures := by
  cases result : pick capture pattern rows with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨datum, present, args, matched⟩
      have missed := (pick_none_iff capture pattern rows).mp result datum present
      rw [matched] at missed
      cases missed
  | some pair =>
      obtain ⟨selected, rest⟩ := pair
      obtain ⟨present, matched, _⟩ := pick_sound capture pattern result
      exact ⟨fun _ => ⟨selected.datum, present, selected.captures, matched⟩, fun _ => rfl⟩

variable [DecidableEq Ch]

def Fits (cache : Ch → List (Datum Val)) (slot : Ch × Pat) (selected : Match Val Arg) : Prop :=
  selected.datum ∈ cache slot.1 ∧ capture slot.2 selected.datum.raw = some selected.captures

/-- Scan in visit order. Returning `none` early preserves the Rust
worker's final Option packet: after any missing bind its collected
result is already `none`, and all cache edits are speculative. -/
def scan : List (Ch × Pat) → (Ch → List (Datum Val)) → Option (List (Match Val Arg))
  | [], _ => some []
  | bind :: rest, cache =>
      match pick capture bind.2 (cache bind.1) with
      | none => none
      | some (selected, remaining) =>
          (scan rest (Function.update cache bind.1 remaining)).map (selected :: ·)

private theorem scan_sound :
    ∀ {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)} {packet : List (Match Val Arg)},
      scan capture binds cache = some packet → List.Forall₂ (Fits capture cache) binds packet
  | [], _, packet, compiled => by
      simp only [scan, Option.some.injEq] at compiled
      subst packet
      exact .nil
  | bind :: binds, cache, packet, compiled => by
      cases here : pick capture bind.2 (cache bind.1) with
      | none => simp [scan, here] at compiled
      | some pair =>
          obtain ⟨head, remaining⟩ := pair
          simp only [scan, here, Option.map_eq_some_iff] at compiled
          obtain ⟨earlier, tail, rfl⟩ := compiled
          obtain ⟨present, matched, subset⟩ := pick_sound capture bind.2 here
          refine .cons ⟨present, matched⟩ ((scan_sound tail).imp ?_)
          intro slot row witnessed
          refine ⟨?_, witnessed.2⟩
          by_cases same : slot.1 = bind.1
          · rw [same]
            have membership := witnessed.1
            rw [same, Function.update_self] at membership
            exact subset membership
          · simpa only [Function.update_of_ne same] using witnessed.1

private theorem scan_isSome_iff_of_distinct :
    ∀ (binds : List (Ch × Pat)) (cache : Ch → List (Datum Val)),
      (binds.map Prod.fst).Nodup →
      ((scan capture binds cache).isSome ↔
        ∀ slot ∈ binds, ∃ datum ∈ cache slot.1, ∃ args, capture slot.2 datum.raw = some args)
  | [], _, _ => by simp [scan]
  | bind :: binds, cache, distinct => by
      have apart := List.nodup_cons.mp distinct
      cases here : pick capture bind.2 (cache bind.1) with
      | none =>
          simp only [scan, here, Option.isSome_none, Bool.false_eq_true, false_iff]
          intro all
          have found := (pick_isSome_iff capture bind.2 _).mpr (all bind List.mem_cons_self)
          simp [here] at found
      | some pair =>
          obtain ⟨found, remaining⟩ := pair
          have same (slot : Ch × Pat) (member : slot ∈ binds) :
              Function.update cache bind.1 remaining slot.1 = cache slot.1 := by
            apply Function.update_of_ne
            intro equal
            exact apart.1 (equal ▸ List.mem_map_of_mem member)
          have head := (pick_isSome_iff capture bind.2 (cache bind.1)).mp (by simp [here])
          rw [scan, here, Option.isSome_map,
            scan_isSome_iff_of_distinct binds _ apart.2, List.forall_mem_cons]
          constructor
          · intro tail
            exact ⟨head, fun slot member => same slot member ▸ tail slot member⟩
          · rintro ⟨_, tail⟩ slot member
            exact (same slot member).symm ▸ tail slot member

def packet (binds : List (Ch × Pat)) (cache : Ch → List (Datum Val)) : Option (List (Match Val Arg)) :=
  (scan capture binds.reverse cache).map List.reverse

private theorem scan_view_congr (binds : List (Ch × Pat)) (left right : Ch → List (Datum Val))
    (same : ∀ slot ∈ binds, left slot.1 = right slot.1) :
    scan capture binds left = scan capture binds right := by
  induction binds generalizing left right with
  | nil => rfl
  | cons slot tail ih =>
    rw [scan, scan, same slot List.mem_cons_self]
    split
    · rfl
    · rw [ih]
      intro bind covered
      by_cases shared : bind.1 = slot.1
      · simp [shared]
      · simpa only [Function.update_of_ne shared] using same bind (List.mem_cons_of_mem _ covered)

/-- Retaining a selected occurrence is not enough to retain the native
choice. The ordered candidate views on all resolved bind channels do
suffice, even when the scan fails or two binds alias. -/
theorem packet_view_congr (binds : List (Ch × Pat)) (left right : Ch → List (Datum Val))
    (same : ∀ slot ∈ binds, left slot.1 = right slot.1) :
    packet capture binds left = packet capture binds right := by
  unfold packet
  rw [scan_view_congr capture binds.reverse left right (fun slot member =>
    same slot (List.mem_reverse.mp member))]

/-- Every returned slot witnesses its original bind and unchanged raw row,
even when different channel expressions resolve to the same channel. -/
theorem packet_sound {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)}
    {selected : List (Match Val Arg)} (compiled : packet capture binds cache = some selected) :
    List.Forall₂ (Fits capture cache) binds selected := by
  obtain ⟨visited, computed, rfl⟩ := Option.map_eq_some_iff.mp compiled
  have supported := List.rel_reverse (scan_sound capture computed)
  simpa only [List.reverse_reverse] using supported

/-- Complete on the fixed view when the resolved channels are distinct.
This requires separation after channel evaluation and unbundling, not
just distinct normalized source expressions. -/
theorem packet_isSome_iff_of_distinct
    (binds : List (Ch × Pat)) (cache : Ch → List (Datum Val)) (distinct : (binds.map Prod.fst).Nodup) :
    (packet capture binds cache).isSome ↔
      ∀ slot ∈ binds, ∃ datum ∈ cache slot.1, ∃ args, capture slot.2 datum.raw = some args := by
  have reversed : (binds.reverse.map Prod.fst).Nodup := by
    simpa only [List.map_reverse, List.nodup_reverse] using distinct
  simp only [packet, Option.isSome_map, scan_isSome_iff_of_distinct capture binds.reverse cache reversed,
    List.mem_reverse]

theorem packet_accepts {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)}
    {selected : List (Match Val Arg)} (compiled : packet capture binds cache = some selected) :
    Accepts (fun pattern datum => (capture pattern datum).isSome) binds (selected.map fun row => row.datum.raw) := by
  unfold Accepts
  rw [List.forall₂_map_right_iff]
  exact (packet_sound capture compiled).imp fun _ _ supported => by simp [supported.2]

/-! ## An arriving send is a candidate, not yet a stored row -/

/-- The produce path prepends its incoming message to the selected channel
cache. It carries the sentinel used by the store, not a physical row index. -/
def withOffer (cache : Ch → List (Datum Val)) (channel : Ch) (value : Val)
    (persistent : Bool) : Ch → List (Datum Val) :=
  Function.update cache channel (⟨value, -1, persistent⟩ :: cache channel)

private theorem mem_withOffer {cache : Ch → List (Datum Val)} {channel source : Ch}
    {value : Val} {persistent : Bool} {datum : Datum Val}
    (inside : datum ∈ withOffer cache channel value persistent source) :
    datum ∈ cache source ∨ (source = channel ∧ datum = ⟨value, -1, persistent⟩) := by
  by_cases same : source = channel
  · subst source
    rw [withOffer, Function.update_self, List.mem_cons] at inside
    exact inside.elim (fun equal => Or.inr ⟨rfl, equal⟩) Or.inl
  · rw [withOffer, Function.update_of_ne same] at inside
    exact Or.inl inside

private theorem paired_mem_left {A B : Type*} {R : A → B → Prop}
    {left : List A} {right : List B} (pairs : List.Forall₂ R left right) :
    ∀ a ∈ left, ∃ b ∈ right, R a b := by
  induction pairs with
  | nil => simp
  | @cons a b moreLeft moreRight relation _ later =>
    intro item inside
    rcases List.mem_cons.mp inside with rfl | tail
    · exact ⟨b, List.mem_cons_self, relation⟩
    · obtain ⟨chosen, present, matched⟩ := later item tail
      exact ⟨chosen, List.mem_cons_of_mem b present, matched⟩

private theorem paired_zip {A B : Type*} {R : A → B → Prop}
    {left : List A} {right : List B} (pairs : List.Forall₂ R left right) :
    ∀ pair ∈ left.zip right, R pair.1 pair.2 := by
  induction pairs with
  | nil => simp
  | @cons a b moreLeft moreRight relation _ later =>
    intro pair inside
    rw [List.zip_cons_cons] at inside
    rcases List.mem_cons.mp inside with rfl | tail
    · exact relation
    · exact later pair tail

/-- At a quiet cut, a previously blocked join on distinct channels cannot
be woken using only old data. The distinctness hypothesis is on resolved
channels; pre-normalization syntax alone does not supply it. -/
theorem arrival_used_of_blocked
    {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)} {selected : List (Match Val Arg)}
    {channel : Ch} {value : Val} {persistent : Bool}
    (distinct : (binds.map Prod.fst).Nodup)
    (blocked : packet capture binds cache = none)
    (delivered : packet capture binds (withOffer cache channel value persistent) = some selected) :
    ∃ row ∈ selected, row.datum = ⟨value, -1, persistent⟩ := by
  by_contra unused
  have oldMatches : ∀ slot ∈ binds, ∃ datum ∈ cache slot.1,
      ∃ args, capture slot.2 datum.raw = some args := by
    intro slot present
    obtain ⟨chosen, used, fits⟩ := paired_mem_left (packet_sound capture delivered) slot present
    refine ⟨chosen.datum, ?_, chosen.captures, fits.2⟩
    rcases mem_withOffer fits.1 with old | ⟨_, incoming⟩
    · exact old
    · exact False.elim (unused ⟨chosen, used, incoming⟩)
  have possible := (packet_isSome_iff_of_distinct capture binds cache distinct).mpr oldMatches
  rw [blocked] at possible
  cases possible

section LockedCommit

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Commit Enabled fire)

/-- Only nonnegative indices are stored rows. The persistence flag
separates takes from retained reads of those rows. -/
def storedKeys (retain : Bool) (binds : List (Ch × Pat)) (selected : List (Match Val Arg)) :
    List (Ch × Int) :=
  (binds.zip selected).filterMap fun (slot, row) =>
    if 0 ≤ row.datum.index ∧ row.datum.persistent = retain then some (slot.1, row.datum.index) else none

omit [DecidableEq Ch] in
theorem mem_storedKeys {retain : Bool} {binds : List (Ch × Pat)} {selected : List (Match Val Arg)}
    {key : Ch × Int} (found : key ∈ storedKeys retain binds selected) :
    ∃ slot row, (slot, row) ∈ binds.zip selected ∧
      0 ≤ row.datum.index ∧ row.datum.persistent = retain ∧ (slot.1, row.datum.index) = key := by
  obtain ⟨⟨slot, row⟩, present, emitted⟩ := List.mem_filterMap.mp found
  dsimp at emitted
  split at emitted
  · rename_i h
    exact ⟨slot, row, present, h.1, h.2, Option.some.inj emitted⟩
  · cases emitted

omit [DecidableEq Ch] in
theorem storedKeys_channel_sublist (retain : Bool) :
    ∀ (binds : List (Ch × Pat)) (selected : List (Match Val Arg)),
      List.Sublist ((storedKeys retain binds selected).map Prod.fst) (binds.map Prod.fst)
  | [], _ => .slnil
  | _ :: _, [] => List.nil_sublist _
  | bind :: binds, row :: selected => by
      have tail := storedKeys_channel_sublist retain binds selected
      by_cases stored : 0 ≤ row.datum.index ∧ row.datum.persistent = retain
      · simpa [storedKeys, stored] using tail.cons_cons bind.1
      · simpa [storedKeys, stored] using tail.cons bind.1

private def eraseStoredAt {Row : Type*} (store : Ch → List Row) (key : Ch × Int) : Ch → List Row :=
  if 0 ≤ key.2 then Function.update store key.1 ((store key.1).eraseIdx key.2.toNat) else store

/-- Array deletion at the locked cut, with indices from the packet. The
caller supplies the deletion order; negative indices are not stored. -/
def applyStoredRemovals {Row : Type*} : List (Ch × Int) → (Ch → List Row) → Ch → List Row
  | [], store => store
  | key :: rest, store => applyStoredRemovals rest (eraseStoredAt store key)

theorem unselected_channel_unchanged {Row : Type*}
    (keys : List (Ch × Int)) (store : Ch → List Row) (channel : Ch)
    (notMem : channel ∉ keys.map Prod.fst) :
    applyStoredRemovals keys store channel = store channel := by
  induction keys generalizing store with
  | nil => rfl
  | cons key rest earlier =>
      have different : channel ≠ key.1 := fun same => notMem (by simp [same])
      rw [applyStoredRemovals, earlier _ (fun member => notMem (List.mem_cons_of_mem _ member))]
      unfold eraseStoredAt
      split
      · exact Function.update_of_ne different _ _
      · rfl

/-- With distinctly resolved channels, array removal uses the original
index in each bucket in any permutation of the selected keys. There
cannot be another deletion in that bucket to shift the chosen index. -/
theorem stored_removal_reads_original_index {Row : Type*}
    {keys : List (Ch × Int)} {view : Ch → List Row} {channel : Ch} {index : Int}
    (distinct : (keys.map Prod.fst).Nodup) (chosen : (channel, index) ∈ keys) (stored : 0 ≤ index) :
    applyStoredRemovals keys view channel = (view channel).eraseIdx index.toNat := by
  induction keys generalizing view with
  | nil => cases chosen
  | cons head rest earlier =>
      obtain ⟨source, position⟩ := head
      have apart := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp chosen with first | later
      · cases first
        rw [applyStoredRemovals, unselected_channel_unchanged _ _ _ apart.1]
        simp [eraseStoredAt, stored]
      · have seen : channel ∈ rest.map Prod.fst := List.mem_map_of_mem later
        have different : channel ≠ source := fun same => apart.1 (same ▸ seen)
        rw [applyStoredRemovals, earlier apart.2 later]
        unfold eraseStoredAt
        split
        · rw [Function.update_of_ne different]
        · rfl

/-- In the no-alias fragment, the selected data deletion preserves
original indices for every order, in particular the Rust ordering. -/
theorem packet_deletion_uses_original_index {Row : Type*}
    {binds : List (Ch × Pat)} {selected : List (Match Val Arg)}
    {keys : List (Ch × Int)} (view : Ch → List Row) (channel : Ch) (index : Int)
    (distinct : (binds.map Prod.fst).Nodup) (ordered : keys.Perm (storedKeys false binds selected))
    (chosen : (channel, index) ∈ keys) :
    applyStoredRemovals keys view channel = (view channel).eraseIdx index.toNat := by
  have stored := mem_storedKeys (ordered.mem_iff.mp chosen)
  obtain ⟨slot, row, _, valid, _, equal⟩ := stored
  have sameIndex : row.datum.index = index := congrArg Prod.snd equal
  have atIndex : 0 ≤ index := sameIndex ▸ valid
  exact stored_removal_reads_original_index
    ((ordered.map Prod.fst).nodup_iff.mpr ((storedKeys_channel_sublist false binds selected).nodup distinct))
    chosen atIndex

def lockedDataCommit (binds : List (Ch × Pat)) (selected : List (Match Val Arg)) :
    Commit (Ch × Int) Val :=
  ⟨(storedKeys false binds selected).toFinset, (storedKeys true binds selected).toFinset, ∅, []⟩

/-- The stored part of a successful packet is an admitted occurrence
selection. Agreement with actual array deletion is the separate
distinct-channel law above. The receiver and later publications are
outside this data footprint. The indexed cache must represent the live
keys and their unique datum metadata. -/
theorem locked_data_admitted
    {binds : List (Ch × Pat)} {cache frontier : Ch → List (Datum Val)} {selected : List (Match Val Arg)}
    (live : Finset (Ch × Int))
    (label : Ch × Int → Val)
    (represented : ∀ source datum, datum ∈ cache source → (source, datum.index) ∈ live)
    (indexDefines : ∀ source first second,
      first ∈ cache source → second ∈ cache source → first.index = second.index → first = second)
    (stored : ∀ source datum, datum ∈ frontier source → 0 ≤ datum.index → datum ∈ cache source)
    (delivered : packet capture binds frontier = some selected) :
    Enabled label live (lockedDataCommit binds selected) := by
  have fits := paired_zip (packet_sound capture delivered)
  have footprint {retain : Bool} {key : Ch × Int} (inside : key ∈ storedKeys retain binds selected) :
      ∃ datum ∈ cache key.1, datum.index = key.2 ∧ datum.persistent = retain := by
    obtain ⟨slot, row, selected, keptIndex, flag, rfl⟩ := mem_storedKeys inside
    exact ⟨row.datum, stored slot.1 row.datum (fits (slot, row) selected).1 keptIndex, rfl, flag⟩
  have included (retain : Bool) : (storedKeys retain binds selected).toFinset ⊆ live := by
    intro key member
    obtain ⟨datum, present, indexed, _⟩ := footprint (List.mem_toFinset.mp member)
    simpa only [indexed, Prod.mk.eta] using represented key.1 datum present
  refine ⟨included false, included true, ?_, Finset.disjoint_empty_left _, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro key removed read
    obtain ⟨gone, old, indexed, linear⟩ := footprint (List.mem_toFinset.mp removed)
    obtain ⟨copy, still, index', constant⟩ := footprint (List.mem_toFinset.mp read)
    have same := indexDefines key.1 gone copy old still (indexed.trans index'.symm)
    rw [same, constant] at linear
    cases linear
  · intro query member
    cases member

theorem locked_data_admitted_with_offer
    {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)} {selected : List (Match Val Arg)}
    {channel : Ch} {value : Val} {persistent : Bool} (live : Finset (Ch × Int))
    (label : Ch × Int → Val)
    (represented : ∀ source datum, datum ∈ cache source → (source, datum.index) ∈ live)
    (indexDefines : ∀ source first second,
      first ∈ cache source → second ∈ cache source → first.index = second.index → first = second)
    (delivered : packet capture binds (withOffer cache channel value persistent) = some selected) :
    Enabled label live (lockedDataCommit binds selected) := by
  apply locked_data_admitted capture live label represented indexDefines _ delivered
  intro source datum present stored
  rcases mem_withOffer present with old | ⟨_, incoming⟩
  · exact old
  · rw [incoming] at stored
    change (0 : Int) ≤ -1 at stored
    omega

/-- The locked produce path takes an ordinary waiting receipt or reads a
persistent one. Waiting keys are tagged apart from data indices. -/
def parkedProduceCommit {Wait : Type*} (binds : List (Ch × Pat)) (selected : List (Match Val Arg))
    (waiting : Wait) (persistent : Bool) : Commit ((Ch × Int) ⊕ Wait) Val :=
  let data := lockedDataCommit binds selected
  ⟨data.taken.disjSum (if persistent then ∅ else {waiting}),
    data.kept.disjSum (if persistent then {waiting} else ∅), ∅, []⟩

/-- The data cut and the installed receiver form one admitted physical
commit. No receiver whose key is not present can supply this extra footprint. -/
theorem parked_produce_admitted {Wait : Type*}
    {binds : List (Ch × Pat)} {selected : List (Match Val Arg)} {waiters : Finset Wait}
    {live : Finset (Ch × Int)} {dataLabel : Ch × Int → Val}
    (waitingLabel : Wait → Val) (waiting : Wait) (persistent : Bool)
    (parked : waiting ∈ waiters)
    (dataReady : Enabled dataLabel live (lockedDataCommit binds selected)) :
    Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters)
      (parkedProduceCommit binds selected waiting persistent) := by
  refine ⟨Finset.disjSum_mono dataReady.taken_subset (by cases persistent <;> simp [parked]),
    Finset.disjSum_mono dataReady.kept_subset (by cases persistent <;> simp [parked]),
    ?_, Finset.disjoint_empty_left _, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro key taken kept
    cases key with
    | inl data =>
        exact Finset.disjoint_left.mp dataReady.apart
          (Finset.inl_mem_disjSum.mp taken) (Finset.inl_mem_disjSum.mp kept)
    | inr receiver =>
        cases persistent <;> simp [parkedProduceCommit] at taken kept
  · intro check member
    cases member

theorem parked_produce_projects {Wait : Type*} [DecidableEq Wait]
    (binds : List (Ch × Pat)) (selected : List (Match Val Arg)) (live : Finset (Ch × Int))
    (waiters : Finset Wait) (waiting : Wait) (persistent : Bool) :
    let after := fire (live.disjSum waiters) (parkedProduceCommit binds selected waiting persistent)
    after.toLeft = fire live (lockedDataCommit binds selected) ∧
    after.toRight = if persistent then waiters else waiters.erase waiting := by
  constructor
  · simp [fire, parkedProduceCommit, lockedDataCommit, Finset.toLeft_sdiff]
  · ext w
    cases persistent <;> simp [fire, parkedProduceCommit]
    exact and_comm

end LockedCommit

/-- Project a real selected packet into the existing settled receipt
rules. Preparation retains the values in bind order; the supplied body
interpretation is responsible for executing its matched captures. -/
theorem packet_prepares_transform_receipt
    {K : Type*} [DecidableEq Val] [DecidableEq Pat] [DecidableEq K]
    (body : K → List Val → Multiset (RhoLbl Ch Val Pat K))
    (kind : Kind) (first : Ch × Pat) (rest : List (Ch × Pat)) (continuation : K)
    (cache : Ch → List (Datum Val)) (selected : List (Match Val Arg))
    (compiled : packet capture (first :: rest) cache = some selected) :
    ∃ rule : Rule (RhoLbl Ch Val Pat K),
      rule.redex = .recv (.receipt kind first rest continuation) ::ₘ
        msgs .msg (first :: rest) (selected.map fun row => row.datum.raw) ∧
      rule.make = body continuation (selected.map fun row => row.datum.raw) ∧
      RhoRule (fun pat value => (capture pat value).isSome) body rule ∧
      Fires (trRows (fun pat value => (capture pat value).isSome)
        fun k vals => (body k vals).map encode) (rule.mapPos encode) := by
  have allowed := packet_accepts capture compiled
  have lowers {rule : Rule (RhoLbl Ch Val Pat K)}
      (authorizes : RhoRule (fun pat value => (capture pat value).isSome) body rule) :
      Fires (trRows (fun pat value => (capture pat value).isSome)
        fun k vals => (body k vals).map encode) (rule.mapPos encode) :=
    (rholang_correspond (sat := fun pat value => (capture pat value).isSome) (body := body)).forward _ authorizes
  cases kind with
  | linear =>
      have accepted := RhoRule.linear (b := first) (bs := rest) (k := continuation) (body := body) allowed
      exact ⟨_, by simp [Rule.redex], rfl, accepted, lowers accepted⟩
  | repeated =>
      have accepted := RhoRule.repeated (b := first) (bs := rest) (k := continuation) (body := body) allowed
      exact ⟨_, by simp [Rule.redex, add_comm], rfl, accepted, lowers accepted⟩
  | peek =>
      have accepted := RhoRule.peek (b := first) (bs := rest) (k := continuation) (body := body) allowed
      exact ⟨_, by simp [Rule.redex], rfl, accepted, lowers accepted⟩

/-- The actual dispatch worker pushes captures in packet order, then does
de Bruijn lookups from the end. It does not push the raw datums. -/
def dispatchEnv (selected : List (Match Val Arg)) : List Arg :=
  (selected.flatMap Match.captures).reverse

theorem dispatch_lookup (selected : List (Match Val Arg)) (index : Nat)
    (inside : index < (dispatchEnv selected).length) :
    (dispatchEnv selected)[index] =
      (selected.flatMap Match.captures)[(selected.flatMap Match.captures).length - 1 - index]'(by
        have nonempty : 0 < (selected.flatMap Match.captures).length :=
          lt_of_le_of_lt (Nat.zero_le _) (by simpa only [dispatchEnv, List.length_reverse] using inside)
        omega) :=
  List.getElem_reverse inside

/-! ## Preparing the body without capturing its received slots -/

/-- The contiguous part of the interpreter's environment at a given shift,
in mathematical integers; machine-integer bounds are a separate check. -/
def shiftedLookup (stored : List Arg) (shift index : Nat) : Option Arg :=
  let key : Int := (stored.length : Int) + shift - index - 1
  if key < 0 then none else stored[key.toNat]?

/-- Before dispatch, the incoming slots are outside the ambient
environment. Shifting for the receive is not a lookup into that packet. -/
theorem preparation_does_not_fill_received_slots (stored : List Arg)
    (ambientShift : Nat) {received index : Nat} (inside : index < received) :
    shiftedLookup stored (ambientShift + received) index = none := by
  have past : (stored.length : Int) ≤ (stored.length : Int) + (ambientShift + received) - index - 1 := by omega
  unfold shiftedLookup
  rw [if_neg (by omega)]
  apply List.getElem?_eq_none
  omega

theorem preparation_preserves_ambient_lookup (stored : List Arg) (ambientShift received index : Nat) :
    shiftedLookup stored (ambientShift + received) (received + index) =
      shiftedLookup stored ambientShift index := by
  have key : (stored.length : Int) + ((ambientShift + received : Nat) : Int) -
      ((received + index : Nat) : Int) - 1 = (stored.length : Int) + ambientShift - index - 1 := by omega
  simp only [shiftedLookup, key]

/-! ## Dispatch scope and private binders -/

/-- The input to a Rholang body evaluator. Installations are in push order,
not de Bruijn order. The random state belongs to this body invocation. -/
structure EvalScope (Arg Supply : Type*) where
  stored : List Arg
  shift : Nat
  random : Supply
  deriving DecidableEq

theorem pushed_lookup_below_shift (stored added : List Arg) {shift index : Nat}
    (below : index < shift) : shiftedLookup (stored ++ added) shift index = none := by
  unfold shiftedLookup
  rw [if_neg (by omega)]
  apply List.getElem?_eq_none
  omega

theorem pushed_lookup_new (stored added : List Arg) (shift : Nat) {index : Nat}
    (inside : index < added.length) :
    shiftedLookup (stored ++ added) shift (shift + index) = added[added.length - index - 1]? := by
  simp only [shiftedLookup, List.length_append]
  rw [if_neg (by omega), List.getElem?_append_right (by omega)]
  congr 1
  omega

theorem pushed_lookup_ambient (stored added : List Arg) {shift index : Nat} (bound : shift ≤ index) :
    shiftedLookup (stored ++ added) shift (added.length + index) = shiftedLookup stored shift index := by
  have key : ((stored.length + added.length : Nat) : Int) + shift -
      ((added.length + index : Nat) : Int) - 1 = (stored.length : Int) + shift - index - 1 := by omega
  simp only [shiftedLookup, List.length_append, key]
  split
  · rfl
  · exact List.getElem?_append_left (by omega)

theorem shiftedLookup_unshifted (stored : List Arg) (index : Nat) :
    shiftedLookup stored 0 index = stored.reverse[index]? := by
  by_cases inside : index < stored.length
  · have inside' : index < stored.reverse.length := by simpa
    unfold shiftedLookup
    rw [if_neg (by omega), List.getElem?_eq_getElem inside', List.getElem_reverse]
    have key : ((stored.length : Int) + (0 : Nat) - index - 1).toNat =
        stored.length - 1 - index := by omega
    rw [key, List.getElem?_eq_getElem]
  · rw [shiftedLookup, if_pos (by omega), List.getElem?_eq_none]
    simpa using inside

/-- A successful nonempty packet starts a process body in an empty ambient
scope. Matching changes the data's captured values, not its random state.
The reducer merges the continuation's seed before the data seeds in bind
order. The two mandatory operands express the native merger's arity floor. -/
def dispatchScope {Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (receiverSeed : Supply)
    (first : Match Val Arg) (rest : List (Match Val Arg)) : EvalScope Arg Supply :=
  ⟨(first :: rest).flatMap Match.captures, 0,
    merge receiverSeed (randomOf first.datum.raw) (rest.map fun row => randomOf row.datum.raw)⟩

theorem dispatch_scope_lookup {Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (receiverSeed : Supply)
    (first : Match Val Arg) (rest : List (Match Val Arg)) (index : Nat) :
    shiftedLookup (dispatchScope randomOf merge receiverSeed first rest).stored
      (dispatchScope randomOf merge receiverSeed first rest).shift index =
      (dispatchEnv (first :: rest))[index]? :=
  shiftedLookup_unshifted _ _

/-- Process dispatch prepares an invocation, not a new store row. A
nonempty receive cannot produce the empty operand vector of a bad merge. -/
def processDispatch {Body Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (body : Body) (receiverSeed : Supply) :
    List (Match Val Arg) → Option (Body × EvalScope Arg Supply)
  | [] => none
  | first :: rest => some (body, dispatchScope randomOf merge receiverSeed first rest)

theorem process_dispatch_of_packet {Body Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (body : Body) (receiverSeed : Supply)
    (firstBind : Ch × Pat) (otherBinds : List (Ch × Pat)) (view : Ch → List (Datum Val))
    {selected : List (Match Val Arg)}
    (delivered : packet capture (firstBind :: otherBinds) view = some selected) :
    ∃ scope, processDispatch randomOf merge body receiverSeed selected = some (body, scope) ∧
      ∀ i, shiftedLookup scope.stored scope.shift i = (dispatchEnv selected)[i]? := by
  have sound := packet_sound capture delivered
  cases sound with
  | cons _ _ =>
    exact ⟨_, rfl, dispatch_scope_lookup randomOf merge receiverSeed _ _⟩

/-- Forward draws: the next body gets the state after the last draw,
not the seed at entry. No injectivity assumption about the generator. -/
def drawBindings {Supply : Type*} (draw : Supply → Arg × Supply) :
    Nat → Supply → List Arg × Supply
  | 0, seed => ([], seed)
  | n + 1, seed =>
    let (name, next) := draw seed
    let (names, final) := drawBindings draw n next
    (name :: names, final)

@[simp] theorem drawBindings_length {Supply : Type*} (draw : Supply → Arg × Supply) :
    ∀ (n : Nat) (seed : Supply), (drawBindings draw n seed).1.length = n
  | 0, _ => rfl
  | n + 1, seed => by simpa [drawBindings] using drawBindings_length draw n (draw seed).2

theorem drawBindings_append {Supply : Type*} (draw : Supply → Arg × Supply)
    (m n : Nat) (seed : Supply) :
    let initial := drawBindings draw m seed
    let sequel := drawBindings draw n initial.2
    drawBindings draw (m + n) seed = (initial.1 ++ sequel.1, sequel.2) := by
  induction m generalizing seed with
  | zero => simp [drawBindings]
  | succ m ih =>
    rw [Nat.succ_add]
    simpa only [drawBindings, List.cons_append] using
      congrArg (fun (r : List Arg × Supply) => ((draw seed).1 :: r.1, r.2)) (ih (draw seed).2)

/-- The installed URI table takes precedence over normalizer injections.
The injection check supplies the native missing/malformed error. -/
def resolveNewUri {Uri Fault : Type*} (registry : Uri → Option Arg)
    (injection : Uri → Except Fault Arg) (uri : Uri) : Except Fault Arg :=
  match registry uri with
  | some installed => .ok installed
  | none => injection uri

/-- Opening a normalized `new` with `privateCount` plain binders and the
given URIs. The normalized total is their sum. Charge once for the total;
install the drawn names, then resolved URI values. Failed resolution
never starts the body and does not roll back the charge. Locking and
accounting internals are the supplied charge operation; the draw embeds a
native private ID as an evaluator value. -/
def openNew {Uri Body Supply Credit Fault : Type*}
    (charge : Nat → Credit → Credit × Except Fault Unit) (draw : Supply → Arg × Supply)
    (resolve : Uri → Except Fault Arg)
    (privateCount : Nat) (uris : List Uri) (body : Body) (scope : EvalScope Arg Supply)
    (credit : Credit) : Credit × Except Fault (Body × EvalScope Arg Supply) :=
  let (left, paid) := charge (2 * (privateCount + uris.length) + 10) credit
  (left, match paid with
    | .error fault => .error fault
    | .ok () =>
      let (names, next) := drawBindings draw privateCount scope.random
      match uris.mapM resolve with
      | .error fault => .error fault
      | .ok resolved => .ok (body, ⟨scope.stored ++ names ++ resolved, scope.shift, next⟩))

theorem open_new_body_iff {Uri Body Supply Credit Fault : Type*}
    (charge : Nat → Credit → Credit × Except Fault Unit) (draw : Supply → Arg × Supply)
    (resolve : Uri → Except Fault Arg)
    (privateCount : Nat) (uris : List Uri) (body code : Body) (scope opened : EvalScope Arg Supply)
    (credit left : Credit) :
    openNew charge draw resolve privateCount uris body scope credit = (left, .ok (code, opened)) ↔
    charge (2 * (privateCount + uris.length) + 10) credit = (left, .ok ()) ∧ code = body ∧
      ∃ resolved, uris.mapM resolve = .ok resolved ∧
        let (names, next) := drawBindings draw privateCount scope.random
        opened = ⟨scope.stored ++ names ++ resolved, scope.shift, next⟩ := by
  cases payment : charge (2 * (privateCount + uris.length) + 10) credit with
  | mk remaining paid =>
    cases paid with
    | error fault => simp [openNew, payment]
    | ok accepted =>
      cases accepted
      cases answers : uris.mapM resolve with
      | error fault => simp [openNew, payment, answers]
      | ok resolved =>
        simp [openNew, payment, answers, eq_comm (a := body), eq_comm (a := opened)]

theorem open_new_bad_charge {Uri Body Supply Credit Fault : Type*}
    (charge : Nat → Credit → Credit × Except Fault Unit) (draw : Supply → Arg × Supply)
    (resolve : Uri → Except Fault Arg)
    (n : Nat) (uris : List Uri) (body : Body) (scope : EvalScope Arg Supply)
    (credit left : Credit) (fault : Fault)
    (rejected : charge (2 * (n + uris.length) + 10) credit = (left, .error fault)) :
    openNew charge draw resolve n uris body scope credit = (left, .error fault) := by
  simp [openNew, rejected]

theorem open_new_bad_uri {Uri Body Supply Credit Fault : Type*}
    (charge : Nat → Credit → Credit × Except Fault Unit) (draw : Supply → Arg × Supply)
    (resolve : Uri → Except Fault Arg)
    (n : Nat) (uris : List Uri) (body : Body) (scope : EvalScope Arg Supply)
    (credit left : Credit) (fault : Fault)
    (paid : charge (2 * (n + uris.length) + 10) credit = (left, .ok ()))
    (rejected : uris.mapM resolve = .error fault) :
    openNew charge draw resolve n uris body scope credit = (left, .error fault) := by
  simp [openNew, paid, rejected]

private theorem resolved_length {Uri Fault : Type*} (resolve : Uri → Except Fault Arg) :
    ∀ {uris : List Uri} {resolved : List Arg},
      uris.mapM resolve = .ok resolved → resolved.length = uris.length
  | [], resolved, done => by
    have empty : [] = resolved := Except.ok.inj done
    simp [← empty]
  | uri :: rest, resolved, done => by
    cases first : resolve uri with
    | error fault => simp [List.mapM_cons, first, Bind.bind, Except.bind] at done
    | ok value =>
      cases more : rest.mapM resolve with
      | error fault => simp [List.mapM_cons, first, more, Bind.bind, Except.bind] at done
      | ok values =>
        have same : value :: values = resolved := by
          simpa [List.mapM_cons, first, more, Bind.bind, Except.bind, Pure.pure, Except.pure] using done
        rw [← same, List.length_cons, resolved_length resolve more, List.length_cons]

/-- The body addresses its installed bindings in reverse push order, after
the shift. Plain draws and URI values occupy different intervals. Lifting
an existing readable index by the full binder count preserves its lookup. -/
theorem open_new_lookups {Uri Body Supply Credit Fault : Type*}
    (charge : Nat → Credit → Credit × Except Fault Unit) (draw : Supply → Arg × Supply)
    (resolve : Uri → Except Fault Arg)
    (n : Nat) (uris : List Uri) (body : Body) (scope opened : EvalScope Arg Supply)
    (credit left : Credit)
    (launched : openNew charge draw resolve n uris body scope credit = (left, .ok (body, opened))) :
    ∃ resolved, uris.mapM resolve = .ok resolved ∧
      let plain := (drawBindings draw n scope.random).1
      let lookup := shiftedLookup opened.stored opened.shift
      opened.random = (drawBindings draw n scope.random).2 ∧
      (∀ i < scope.shift, lookup i = none) ∧
      (∀ i < uris.length, lookup (scope.shift + i) = resolved[uris.length - i - 1]?) ∧
      (∀ i < n, lookup (scope.shift + (uris.length + i)) = plain[n - i - 1]?) ∧
      (∀ i, scope.shift ≤ i →
        lookup (n + uris.length + i) = shiftedLookup scope.stored scope.shift i) := by
  obtain ⟨_, _, resolved, solved, rfl⟩ := (open_new_body_iff charge draw resolve n uris body body
    scope opened credit left).mp launched
  have size := resolved_length resolve solved
  refine ⟨resolved, solved, ?_⟩
  dsimp only
  generalize hPlain : (drawBindings draw n scope.random).1 = plain
  have draws : plain.length = n := by rw [← hPlain, drawBindings_length]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro index below
    exact pushed_lookup_below_shift _ _ below
  · intro index inside
    rw [← size] at inside ⊢
    exact pushed_lookup_new _ _ _ inside
  · intro index inside
    rw [← draws] at inside
    rw [← size, ← draws]
    rw [show scope.shift + (resolved.length + index) = resolved.length + (scope.shift + index) by omega]
    rw [pushed_lookup_ambient _ _ (by omega)]
    exact pushed_lookup_new _ _ _ inside
  · intro index bound
    rw [← size, ← draws]
    rw [show plain.length + resolved.length + index = resolved.length + (plain.length + index) by omega]
    rw [pushed_lookup_ambient _ _ (by omega), pushed_lookup_ambient _ _ bound]

/-- Distinct private draws stay distinct as seen through body lookups.
This concerns the plain binders only; installed URIs may intentionally
alias. Freshness against an ambient name support needs a separate
property of the supplied name generator. -/
theorem open_new_private_lookup_injective {Uri Body Supply Credit Fault : Type*}
    (charge : Nat → Credit → Credit × Except Fault Unit) (draw : Supply → Arg × Supply)
    (resolve : Uri → Except Fault Arg)
    (n : Nat) (uris : List Uri) (body : Body) (scope opened : EvalScope Arg Supply)
    (credit left : Credit)
    (launched : openNew charge draw resolve n uris body scope credit = (left, .ok (body, opened)))
    (distinct : (drawBindings draw n scope.random).1.Nodup) {i j : Nat} (hi : i < n) (hj : j < n)
    (equal : shiftedLookup opened.stored opened.shift (scope.shift + (uris.length + i)) =
      shiftedLookup opened.stored opened.shift (scope.shift + (uris.length + j))) : i = j := by
  obtain ⟨_, _, _, _, _, look, _⟩ := open_new_lookups charge draw resolve n uris body scope opened
    credit left launched
  rw [look i hi, look j hj] at equal
  have inRange : n - i - 1 < (drawBindings draw n scope.random).1.length := by
    rw [drawBindings_length]
    omega
  have same := (List.getElem?_inj inRange distinct).mp equal
  omega

/-! ## Atomic surface reads and split peek publication -/

/-- A later produce uses the same resolved endpoint, raw value and flag.
It is a new search request, not an unconditional insertion. -/
abbrev ProduceRequest (Ch Val : Type*) := Ch × Val × Bool

/-- One ordinary produce request for each selected nonpersistent datum,
including the incoming offer when that datum was itself selected. -/
def repostRequests (binds : List (Ch × Pat)) (packet : List (Match Val Arg)) :
    List (ProduceRequest Ch Val) :=
  (binds.zip packet).filterMap fun (bind, selected) =>
    if selected.datum.persistent then none else some (bind.1, selected.datum.raw, false)

/-- Success-path followups of the Rust produce worker, besides dispatch.
Persistent re-produce takes priority over the peek branch. -/
def afterProduce (offered : ProduceRequest Ch Val) (peek : Bool)
    (binds : List (Ch × Pat)) (packet : List (Match Val Arg)) : List (ProduceRequest Ch Val) :=
  if offered.2.2 then [offered] else if peek then repostRequests binds packet else []

/-- A successful active repeated receive launches another consume request
with the original prepared request. This is not the keep operation on
an already installed waiting continuation. -/
def afterConsume {Request : Type*} (request : Request) (persistent peek : Bool)
    (binds : List (Ch × Pat)) (packet : List (Match Val Arg)) :
    Option Request × List (ProduceRequest Ch Val) :=
  if persistent then (some request, []) else (none, if peek then repostRequests binds packet else [])

/-! ## From a locked offer to its workers -/

/-- One join bucket's shuffled continuations and candidate data. The data
is prepared once per bucket, not carried over after a failed trial. -/
abbrev WaitView (Ch Val Wait : Type*) := (Ch → List (Datum Val)) × List Wait

/-- Try the shuffled waiters from last to first within a bucket, starting
each speculative scan at the same view of this offer. -/
def offerGroup {Wait : Type*} (binds : Wait → List (Ch × Pat))
    (offer : ProduceRequest Ch Val) (bucket : WaitView Ch Val Wait) :
    Option (Wait × List (Match Val Arg)) :=
  bucket.2.reverse.findSome? fun w =>
    (packet capture (binds w) (withOffer bucket.1 offer.1 offer.2.1 offer.2.2)).map (w, ·)

/-- The locked produce path tries the join buckets in their lookup order.
The shuffled vectors are inputs; this is not a reshuffling policy. -/
def offerSearch {Wait : Type*} (binds : Wait → List (Ch × Pat))
    (offer : ProduceRequest Ch Val) (groups : List (WaitView Ch Val Wait)) :
    Option (Wait × List (Match Val Arg)) :=
  groups.findSome? (offerGroup capture binds offer)

theorem offer_group_none_iff {Wait : Type*} (binds : Wait → List (Ch × Pat))
    (offer : ProduceRequest Ch Val) (bucket : WaitView Ch Val Wait) :
    offerGroup capture binds offer bucket = none ↔
      ∀ w ∈ bucket.2, packet capture (binds w) (withOffer bucket.1 offer.1 offer.2.1 offer.2.2) = none := by
  simp [offerGroup, List.findSome?_eq_none_iff]

theorem offer_search_none_iff {Wait : Type*} (binds : Wait → List (Ch × Pat))
    (offer : ProduceRequest Ch Val) (groups : List (WaitView Ch Val Wait)) :
    offerSearch capture binds offer groups = none ↔
      ∀ group ∈ groups, ∀ w ∈ group.2,
        packet capture (binds w) (withOffer group.1 offer.1 offer.2.1 offer.2.2) = none := by
  simp only [offerSearch, List.findSome?_eq_none_iff, offer_group_none_iff]

/-- Existence of a matching value at every resolved bind. This is
joint readiness only in the distinct-channel configuration. The
physical packet still records which occurrence each bind selected. -/
def ReadyOn (has : Ch → Val → Prop) (binds : List (Ch × Pat)) : Prop :=
  ∀ bind ∈ binds, ∃ value, has bind.1 value ∧ ∃ args, capture bind.2 value = some args

/-- Coverage for deciding readiness is about possible values on a
named channel. Ordering and physical index identity are separate
obligations for recovering the selected packet. -/
def ViewValues (cache : Ch → List (Datum Val)) (has : Ch → Val → Prop) (channel : Ch) : Prop :=
  ∀ value, (∃ row ∈ cache channel, row.raw = value) ↔ has channel value

def offeredValues (has : Ch → Val → Prop) (offer : ProduceRequest Ch Val) (channel : Ch) (value : Val) : Prop :=
  has channel value ∨ (channel = offer.1 ∧ value = offer.2.1)

theorem ViewValues.with_offer {cache : Ch → List (Datum Val)} {has : Ch → Val → Prop}
    {channel : Ch} (covered : ViewValues cache has channel) (offer : ProduceRequest Ch Val) :
    ViewValues (withOffer cache offer.1 offer.2.1 offer.2.2) (offeredValues has offer) channel := by
  intro raw
  constructor
  · rintro ⟨row, member, rfl⟩
    rcases mem_withOffer member with old | ⟨same, incoming⟩
    · exact .inl ((covered _).mp ⟨row, old, rfl⟩)
    · exact .inr ⟨same, congrArg Datum.raw incoming⟩
  · rintro (old | ⟨rfl, rfl⟩)
    · obtain ⟨row, still, rfl⟩ := (covered raw).mpr old
      refine ⟨row, ?_, rfl⟩
      by_cases same : channel = offer.1
      · subst channel
        simpa only [withOffer, Function.update_self] using
          (List.mem_cons_of_mem (Datum.mk offer.2.1 (-1) offer.2.2) still)
      · simpa only [withOffer, Function.update_of_ne same] using still
    · exact ⟨⟨offer.2.1, -1, offer.2.2⟩, by simp [withOffer], rfl⟩

/-- A complete value view is needed for none queries, even though a found
packet can be checked using only its selected witnesses. -/
theorem packet_isSome_iff_readyOn {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)}
    {has : Ch → Val → Prop} (distinct : (binds.map Prod.fst).Nodup)
    (covered : ∀ bind ∈ binds, ViewValues cache has bind.1) :
    (packet capture binds cache).isSome ↔ ReadyOn capture has binds := by
  rw [packet_isSome_iff_of_distinct capture binds cache distinct]
  constructor
  · intro agreed bind member
    obtain ⟨row, present, args, matched⟩ := agreed bind member
    exact ⟨row.raw, (covered bind member _).mp ⟨row, present, rfl⟩, args, matched⟩
  · intro agreed bind member
    obtain ⟨value, present, args, matched⟩ := agreed bind member
    obtain ⟨row, visible, rfl⟩ := (covered bind member value).mpr present
    exact ⟨row, visible, args, matched⟩

theorem packet_none_iff_not_readyOn {binds : List (Ch × Pat)} {cache : Ch → List (Datum Val)}
    {has : Ch → Val → Prop} (distinct : (binds.map Prod.fst).Nodup)
    (covered : ∀ bind ∈ binds, ViewValues cache has bind.1) :
    packet capture binds cache = none ↔ ¬ ReadyOn capture has binds := by
  have reads := packet_isSome_iff_readyOn capture distinct covered
  cases found : packet capture binds cache <;> simp_all

/-- A produce miss is exactly none queries of an eligible installed receive
after lending the offered value to the scan. Lookup completeness and
data-view completeness are independent: neither can replace the other. -/
theorem offer_search_none_iff_no_wake {Wait : Type*} [DecidableEq Wait]
    (binds : Wait → List (Ch × Pat)) (offer : ProduceRequest Ch Val)
    (groups : List (WaitView Ch Val Wait)) (waiters : Finset Wait) (has : Ch → Val → Prop)
    (index : ∀ w, (w ∈ waiters ∧ offer.1 ∈ (binds w).map Prod.fst) ↔
      ∃ group ∈ groups, w ∈ group.2)
    (distinct : ∀ w ∈ waiters, ((binds w).map Prod.fst).Nodup)
    (covered : ∀ group ∈ groups, ∀ w ∈ group.2, ∀ bind ∈ binds w, ViewValues group.1 has bind.1) :
    offerSearch capture binds offer groups = none ↔
      ∀ w ∈ waiters, offer.1 ∈ (binds w).map Prod.fst →
        ¬ ReadyOn capture (offeredValues has offer) (binds w) := by
  rw [offer_search_none_iff capture]
  constructor
  · intro missed w installed touches
    obtain ⟨group, inside, present⟩ := (index w).mp ⟨installed, touches⟩
    exact (packet_none_iff_not_readyOn capture (distinct w installed)
      (fun bind member => (covered group inside w present bind member).with_offer offer)).mp
      (missed group inside w present)
  · intro missed group inside w present
    obtain ⟨installed, touches⟩ := (index w).mpr ⟨group, inside, present⟩
    exact (packet_none_iff_not_readyOn capture (distinct w installed)
      (fun bind member => (covered group inside w present bind member).with_offer offer)).mpr
      (missed w installed touches)

theorem offer_search_winner_iff {Wait : Type*} {binds : Wait → List (Ch × Pat)}
    {offer : ProduceRequest Ch Val} {groups : List (WaitView Ch Val Wait)}
    {waiting : Wait} {selected : List (Match Val Arg)} :
    offerSearch capture binds offer groups = some (waiting, selected) ↔
    ∃ before group after, groups = before ++ group :: after ∧
      (∀ skipped ∈ before, offerGroup capture binds offer skipped = none) ∧
      ∃ prior later, group.2.reverse = prior ++ waiting :: later ∧
        (∀ w ∈ prior, packet capture (binds w) (withOffer group.1 offer.1 offer.2.1 offer.2.2) = none) ∧
        packet capture (binds waiting) (withOffer group.1 offer.1 offer.2.1 offer.2.2) = some selected := by
  constructor
  · intro found
    obtain ⟨before, group, after, rfl, credited, earlier⟩ := List.findSome?_eq_some_iff.mp found
    obtain ⟨prior, waiter, later, visited, accepted, skipped⟩ := List.findSome?_eq_some_iff.mp credited
    obtain ⟨result, delivered, equal⟩ := Option.map_eq_some_iff.mp accepted
    have waiterEq := congrArg Prod.fst equal
    have resultEq := congrArg Prod.snd equal
    change waiter = waiting at waiterEq
    change result = selected at resultEq
    subst waiter
    subst result
    exact ⟨before, group, after, rfl, earlier, prior, later, visited,
      fun w inside => by simpa using skipped w inside, delivered⟩
  · rintro ⟨before, group, after, layout, earlier, prior, later, visited, skipped, delivered⟩
    apply List.findSome?_eq_some_iff.mpr
    refine ⟨before, group, after, layout, List.findSome?_eq_some_iff.mpr ?_, earlier⟩
    exact ⟨prior, waiting, later, visited, by simp [delivered], fun w inside => by simp [skipped w inside]⟩

private theorem find_some_congr {A B : Type*} {pick other : A → Option B} (xs : List A)
    (same : ∀ x ∈ xs, pick x = other x) : xs.findSome? pick = xs.findSome? other := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findSome?_cons, List.findSome?_cons, same x List.mem_cons_self]
    rw [ih (fun y member => same y (List.mem_cons_of_mem x member))]

/-- For fixed join and waiter orders, a sibling may change channels
outside the candidate search's view. This preserves the entire search
(including failed trials), not merely admission of its former winner. -/
theorem offer_search_view_congr {Wait : Type*} (binds : Wait → List (Ch × Pat))
    (offer : ProduceRequest Ch Val) {left right : List (WaitView Ch Val Wait)}
    (views : List.Forall₂ (fun l r =>
      l.2 = r.2 ∧ ∀ waiting ∈ l.2, ∀ slot ∈ binds waiting, l.1 slot.1 = r.1 slot.1) left right) :
    offerSearch capture binds offer left = offerSearch capture binds offer right := by
  induction views with
  | nil => rfl
  | @cons l r ls rs covered _ ih =>
    have sameGroup : offerGroup capture binds offer l = offerGroup capture binds offer r := by
      unfold offerGroup
      rw [← covered.1]
      apply find_some_congr
      intro waiting visited
      congr 1
      apply packet_view_congr
      intro slot needed
      have same := covered.2 waiting (List.mem_reverse.mp visited) slot needed
      unfold withOffer
      by_cases onOffer : slot.1 = offer.1
      · rw [onOffer] at same ⊢
        simp [same]
      · simpa only [Function.update_of_ne onOffer] using same
    simp only [offerSearch, List.findSome?_cons, sameGroup]
    unfold offerSearch at ih
    rw [ih]

/-! ## Maintaining the live join lookup -/

/-- The two continuation sources and the two ordered join indexes
returned after hot/history lookup. The keys are ordered channel
vectors, not sets of channels. -/
structure JoinIndex (Channel Wait : Type*) where
  ordinary : List Channel → List Wait
  installed : List Channel → Option Wait
  joins : Channel → List (List Channel)
  installedJoins : Channel → List (List Channel)

namespace JoinIndex

variable {Wait : Type*}

def waitersAt (table : JoinIndex Ch Wait) (keys : List Ch) : List Wait :=
  (table.installed keys).toList ++ table.ordinary keys

def keysAt (table : JoinIndex Ch Wait) (channel : Ch) : List (List Ch) :=
  table.installedJoins channel ++ table.joins channel

/-- A bucket can contribute exactly its live waiters. Every nonempty
bucket is found on each of its channels. Empty stale index entries
are harmless for coverage, and entries present in both lookup
sources are not coalesced. -/
structure Covers (table : JoinIndex Ch Wait) (channels : Wait → List Ch) (live : Finset Wait) : Prop where
  bucket : ∀ ks w, w ∈ table.waitersAt ks ↔ w ∈ live ∧ channels w = ks
  unique : ∀ ks, (table.waitersAt ks).Nodup
  routed : ∀ ch ks, ks ∈ table.keysAt ch → ch ∈ ks
  covered : ∀ ch ks, ch ∈ ks → table.waitersAt ks ≠ [] → ks ∈ table.keysAt ch

def empty : JoinIndex Ch Wait := ⟨fun _ => [], fun _ => none, fun _ => [], fun _ => []⟩

omit [DecidableEq Ch] in
theorem empty_covers (channels : Wait → List Ch) :
    (empty : JoinIndex Ch Wait).Covers channels ∅ := by
  constructor <;> simp [empty, waitersAt, keysAt]

/-- Effective ordinary-table identity comparison supplied by the
host. The native duplicate check does not consult installed records
or waiters in different channel vectors. -/
def duplicate {Identity : Type*} [DecidableEq Identity] (table : JoinIndex Ch Wait)
    (identity : Wait → Identity) (keys : List Ch) (request : Wait) : Option Wait :=
  (table.ordinary keys).find? fun old => decide (identity old = identity request)

private def addJoin (index : Ch → List (List Ch)) (keys : List Ch) (channel : Ch) : List (List Ch) :=
  if channel ∈ keys ∧ keys ∉ index channel then keys :: index channel else index channel

private theorem mem_addJoin {index : Ch → List (List Ch)} {keys ks : List Ch} {channel : Ch} :
    ks ∈ addJoin index keys channel ↔ ks ∈ index channel ∨ (ks = keys ∧ channel ∈ keys) := by
  unfold addJoin
  by_cases onKey : channel ∈ keys
  · by_cases already : keys ∈ index channel
    · simp only [onKey, already, not_true_eq_false, and_false, ↓reduceIte, and_true]
      exact ⟨Or.inl, fun h => h.elim id (fun same => same ▸ already)⟩
    · simp [onKey, already, or_comm]
  · simp [onKey]

/-- Store an ordinary blocked request exactly once per native
identity in that bucket. The channel index is ensured in either
case, matching the calls after `put_continuation`. -/
def park {Identity : Type*} [DecidableEq Identity] (table : JoinIndex Ch Wait)
    (identity : Wait → Identity) (keys : List Ch) (request : Wait) : JoinIndex Ch Wait :=
  let rows := match table.duplicate identity keys request with
    | none => request :: table.ordinary keys
    | some _ => table.ordinary keys
  {table with
    ordinary := Function.update table.ordinary keys rows
    joins := addJoin table.joins keys}

theorem park_keys_iff {Identity : Type*} [DecidableEq Identity] (table : JoinIndex Ch Wait)
    (identity : Wait → Identity) (keys : List Ch) (request : Wait) (channel : Ch) (ks : List Ch) :
    ks ∈ (table.park identity keys request).keysAt channel ↔
      ks ∈ table.keysAt channel ∨ (ks = keys ∧ channel ∈ keys) := by
  simp only [keysAt, park, List.mem_append, mem_addJoin, or_assoc]

theorem park_duplicate_waiters {Identity : Type*} [DecidableEq Identity]
    (table : JoinIndex Ch Wait) (identity : Wait → Identity) (keys : List Ch) (request old : Wait)
    (found : table.duplicate identity keys request = some old) (ks : List Ch) :
    (table.park identity keys request).waitersAt ks = table.waitersAt ks := by
  simp [waitersAt, park, found]

theorem park_fresh_waiters {Identity : Type*} [DecidableEq Identity]
    (table : JoinIndex Ch Wait) (identity : Wait → Identity) (keys : List Ch) (request : Wait)
    (missing : table.duplicate identity keys request = none) :
    (table.park identity keys request).waitersAt keys =
      (table.installed keys).toList ++ request :: table.ordinary keys := by
  simp [waitersAt, park, missing]

theorem park_other_waiters {Identity : Type*} [DecidableEq Identity]
    (table : JoinIndex Ch Wait) (identity : Wait → Identity) (keys : List Ch) (request : Wait)
    {ks : List Ch} (other : ks ≠ keys) :
    (table.park identity keys request).waitersAt ks = table.waitersAt ks := by
  simp [waitersAt, park, Function.update_of_ne other]

/-- Parking preserves the existing roster on a duplicate and extends
it by the fresh address otherwise. It also maintains the lookup
coverage required by subsequent sends. -/
theorem park_covers {Identity : Type*} [DecidableEq Identity] [DecidableEq Wait]
    {table : JoinIndex Ch Wait} {channels : Wait → List Ch} {live : Finset Wait}
    (before : table.Covers channels live) (identity : Wait → Identity) (request : Wait)
    (fresh : table.duplicate identity (channels request) request = none → request ∉ live) :
    (table.park identity (channels request) request).Covers channels
      (match table.duplicate identity (channels request) request with
        | none => insert request live
        | some _ => live) := by
  let keys := channels request
  let reached := table.park identity keys request
  have routed : ∀ ch ks, ks ∈ reached.keysAt ch → ch ∈ ks := by
    intro ch ks member
    rcases (park_keys_iff table identity keys request ch ks).mp member with old | ⟨rfl, onKey⟩
    · exact before.routed ch ks old
    · exact onKey
  cases found : table.duplicate identity (channels request) request with
  | some old =>
    have retained (ks : List Ch) : reached.waitersAt ks = table.waitersAt ks :=
      park_duplicate_waiters table identity keys request old found ks
    refine ⟨fun ks w => ?_, fun ks => ?_, routed, ?_⟩
    · rw [retained]
      exact before.bucket ks w
    · rw [retained]; exact before.unique ks
    · intro ch ks onKey witnesses
      apply (park_keys_iff table identity keys request ch ks).mpr
      rw [retained] at witnesses
      exact .inl (before.covered ch ks onKey witnesses)
  | none =>
    have unused := fresh found
    have members (ks : List Ch) (w : Wait) :
        w ∈ reached.waitersAt ks ↔ w ∈ table.waitersAt ks ∨ (w = request ∧ keys = ks) := by
      by_cases same : ks = keys
      · subst ks
        rw [park_fresh_waiters table identity keys request found]
        simp only [waitersAt, List.mem_append, List.mem_cons, and_true]
        tauto
      · rw [park_other_waiters table identity keys request same]
        simp [Ne.symm same]
    refine ⟨?_, ?_, routed, ?_⟩
    · intro ks w
      rw [members, before.bucket, Finset.mem_insert]
      constructor
      · rintro (⟨parked, equal⟩ | ⟨rfl, equal⟩)
        · exact ⟨.inr parked, equal⟩
        · exact ⟨.inl rfl, equal⟩
      · rintro ⟨rfl | parked, equal⟩
        · exact .inr ⟨rfl, equal⟩
        · exact .inl ⟨parked, equal⟩
    · intro ks
      by_cases same : ks = keys
      · subst ks
        rw [park_fresh_waiters table identity keys request found, List.perm_middle.nodup_iff]
        refine List.nodup_cons.mpr ⟨fun old => unused ((before.bucket keys request).mp old).1,
          before.unique keys⟩
      · rw [park_other_waiters table identity keys request same]
        exact before.unique ks
    · intro ch ks onKey witnesses
      apply (park_keys_iff table identity keys request ch ks).mpr
      by_cases same : ks = keys
      · exact .inr ⟨same, same ▸ onKey⟩
      · rw [park_other_waiters table identity keys request same] at witnesses
        exact .inl (before.covered ch ks onKey witnesses)

/-- Prepare one view per lookup position. A bucket appearing in both
indexes is visited twice and may be shuffled differently each time. -/
def offerViews (table : JoinIndex Ch Wait) (channel : Ch)
    (prepare : List Ch → ℕ → WaitView Ch Val Wait) : List (WaitView Ch Val Wait) :=
  (table.keysAt channel).zipIdx.map fun (keys, position) => prepare keys position

omit [DecidableEq Ch] in
private theorem key_in_zip {keys : List (List Ch)} {key : List Ch} :
    key ∈ keys ↔ ∃ stamped ∈ keys.zipIdx, stamped.1 = key := by
  rw [List.exists_mem_zipIdx']
  constructor
  · exact List.getElem_of_mem
  · rintro ⟨i, valid, rfl⟩
    exact List.getElem_mem valid

omit [DecidableEq Ch] in
/-- The receive-lookup coverage premise of the locked produce proof
follows from the maintained index and the actual shuffled vectors.
No ordering or shuffle is inferred from mere membership. -/
theorem offerViews_cover {table : JoinIndex Ch Wait} {channels : Wait → List Ch} {live : Finset Wait}
    (indexed : table.Covers channels live) (channel : Ch)
    (prepare : List Ch → ℕ → WaitView Ch Val Wait)
    (shuffled : ∀ entry ∈ (table.keysAt channel).zipIdx,
      (prepare entry.1 entry.2).2.Perm (table.waitersAt entry.1)) (waiter : Wait) :
    (waiter ∈ live ∧ channel ∈ channels waiter) ↔
      ∃ group ∈ table.offerViews channel prepare, waiter ∈ group.2 := by
  constructor
  · rintro ⟨installed, route⟩
    have member := (indexed.bucket (channels waiter) waiter).mpr ⟨installed, rfl⟩
    have nonempty : table.waitersAt (channels waiter) ≠ [] := by
      intro notMem
      rw [notMem] at member
      cases member
    obtain ⟨entry, located, correct⟩ := key_in_zip.mp (indexed.covered channel _ route nonempty)
    have before : waiter ∈ table.waitersAt entry.1 := correct.symm ▸ member
    exact ⟨prepare entry.1 entry.2, List.mem_map.mpr ⟨entry, located, rfl⟩,
      (shuffled entry located).mem_iff.mpr before⟩
  · rintro ⟨group, located, member⟩
    obtain ⟨entry, indexEntry, rfl⟩ := List.mem_map.mp located
    have before := (shuffled entry indexEntry).mem_iff.mp member
    obtain ⟨installed, keys⟩ := (indexed.bucket entry.1 waiter).mp before
    have routed := indexed.routed channel entry.1 (key_in_zip.mpr ⟨entry, indexEntry, rfl⟩)
    exact ⟨installed, keys.symm ▸ routed⟩

/-- Unlink a selected ordinary receiver, then remove the ordinary
join entry only if the merged bucket has no remaining waiters. An
installed entry is never removed by this operation. -/
def dropOrdinary [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (keys : List Ch) (waiter : Wait) : JoinIndex Ch Wait :=
  let remaining := (table.ordinary keys).erase waiter
  let vacant := (table.installed keys).toList ++ remaining = []
  {table with
    ordinary := Function.update table.ordinary keys remaining
    joins := fun channel => if channel ∈ keys ∧ vacant then (table.joins channel).erase keys else table.joins channel}

theorem drop_waiters_at [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (keys : List Ch) (waiter : Wait) (notInstalled : waiter ∉ (table.installed keys).toList) :
    (table.dropOrdinary keys waiter).waitersAt keys = (table.waitersAt keys).erase waiter := by
  simp only [waitersAt, dropOrdinary, Function.update_self, List.erase_append_right _ notInstalled]

theorem drop_other_waiters [DecidableEq Wait] (table : JoinIndex Ch Wait) (keys : List Ch) (waiter : Wait)
    {other : List Ch} (different : other ≠ keys) :
    (table.dropOrdinary keys waiter).waitersAt other = table.waitersAt other := by
  simp only [waitersAt, dropOrdinary, Function.update_of_ne different]

private theorem drop_keys_subset [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (keys : List Ch) (waiter : Wait) (channel : Ch) {other : List Ch}
    (member : other ∈ (table.dropOrdinary keys waiter).keysAt channel) : other ∈ table.keysAt channel := by
  simp only [keysAt, dropOrdinary, List.mem_append] at member ⊢
  split at member
  · exact member.elim Or.inl (fun kept => .inr (List.mem_of_mem_erase kept))
  · exact member

private theorem drop_keeps_other_keys [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (keys : List Ch) (waiter : Wait) (channel : Ch) {other : List Ch} (different : other ≠ keys)
    (member : other ∈ table.keysAt channel) : other ∈ (table.dropOrdinary keys waiter).keysAt channel := by
  simp only [keysAt, dropOrdinary, List.mem_append] at member ⊢
  split
  · exact member.elim Or.inl (fun already => .inr ((List.mem_erase_of_ne different).mpr already))
  · exact member

theorem drop_nonempty_keeps_index [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (keys : List Ch) (waiter : Wait) (channel : Ch)
    (remaining : (table.dropOrdinary keys waiter).waitersAt keys ≠ []) :
    (table.dropOrdinary keys waiter).keysAt channel = table.keysAt channel := by
  have occupied : (table.installed keys).toList ++ (table.ordinary keys).erase waiter ≠ [] := by
    simpa only [waitersAt, dropOrdinary, Function.update_self] using remaining
  simp [keysAt, dropOrdinary, occupied]

/-- The installed prefix shifts the ordinal of every ordinary
continuation. On a valid selection of an ordinary entry, the native
index deletion removes exactly that stable waiter, not its neighbor. -/
theorem ordinary_slot_deletion [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (keys : List Ch) (waiter : Wait) (index : ℕ)
    (distinct : (table.waitersAt keys).Nodup)
    (selected : (table.waitersAt keys)[index]? = some waiter)
    (notInstalled : waiter ∉ (table.installed keys).toList) :
    let offset := (table.installed keys).toList.length
    offset ≤ index ∧
      (table.ordinary keys).eraseIdx (index - offset) = (table.dropOrdinary keys waiter).ordinary keys := by
  have offset : (table.installed keys).toList.length ≤ index := by
    by_contra tooSmall
    have inside := Nat.lt_of_not_ge tooSmall
    rw [waitersAt, List.getElem?_append_left inside] at selected
    exact notInstalled (List.mem_of_getElem? selected)
  have stored : (table.ordinary keys)[index - (table.installed keys).toList.length]? = some waiter := by
    simpa only [waitersAt, List.getElem?_append_right offset] using selected
  obtain ⟨valid, found⟩ := List.getElem?_eq_some_iff.mp stored
  have unique : (table.ordinary keys).Nodup :=
    (List.sublist_append_right (table.installed keys).toList (table.ordinary keys)).nodup distinct
  refine ⟨offset, ?_⟩
  have erased := unique.erase_getElem _ valid
  rw [found] at erased
  simpa only [dropOrdinary, Function.update_self] using erased.symm

/-- Removing a legal linear selection preserves the exact roster
and complete channel lookup. Persistent delivery leaves the table
unchanged, and does not need this deletion. -/
theorem drop_covers [DecidableEq Wait] {table : JoinIndex Ch Wait}
    {channels : Wait → List Ch} {live : Finset Wait}
    (before : table.Covers channels live) (waiter : Wait)
    (notInstalled : waiter ∉ (table.installed (channels waiter)).toList) :
    (table.dropOrdinary (channels waiter) waiter).Covers channels (live.erase waiter) := by
  let keys := channels waiter
  let after := table.dropOrdinary keys waiter
  have changed := drop_waiters_at table keys waiter notInstalled
  refine ⟨?_, ?_, fun ch ks member => before.routed ch ks (drop_keys_subset table keys waiter ch member), ?_⟩
  · intro ks w
    by_cases key : ks = keys
    · subst ks
      rw [changed, (before.unique keys).mem_erase_iff, before.bucket, Finset.mem_erase, and_assoc]
    · rw [drop_other_waiters table keys waiter key, before.bucket, Finset.mem_erase]
      constructor
      · rintro ⟨member, route⟩
        have other : w ≠ waiter := by
          intro same
          subst w
          exact key route.symm
        exact ⟨⟨other, member⟩, route⟩
      · rintro ⟨⟨_, member⟩, route⟩
        exact ⟨member, route⟩
  · intro ks
    by_cases key : ks = keys
    · subst ks
      rw [changed]
      exact (before.unique keys).erase waiter
    · rw [drop_other_waiters table keys waiter key]
      exact before.unique ks
  · intro ch ks onKey nonempty
    by_cases key : ks = keys
    · subst ks
      have prior : table.waitersAt keys ≠ [] := by
        intro notMem
        apply nonempty
        rw [changed, notMem]
        rfl
      rw [drop_nonempty_keeps_index table keys waiter ch nonempty]
      exact before.covered ch keys onKey prior
    · apply drop_keeps_other_keys table keys waiter ch key
      rw [drop_other_waiters table keys waiter key] at nonempty
      exact before.covered ch ks onKey nonempty

/-- The startup install writes the one installed entry at an ordered
channel vector. The ordinary bucket and its index are untouched. -/
def install (table : JoinIndex Ch Wait) (keys : List Ch) (waiter : Wait) : JoinIndex Ch Wait :=
  {table with
    installed := Function.update table.installed keys (some waiter)
    installedJoins := addJoin table.installedJoins keys}

theorem install_keys_iff (table : JoinIndex Ch Wait) (keys : List Ch) (waiter : Wait) (channel : Ch) (ks : List Ch) :
    ks ∈ (table.install keys waiter).keysAt channel ↔
      ks ∈ table.keysAt channel ∨ (ks = keys ∧ channel ∈ keys) := by
  simp only [keysAt, install, List.mem_append, mem_addJoin]
  tauto

/-- A fresh installed occurrence replaces only the previous installed
entry of that vector. This is the index update after a successful
startup authorization, not a license to install over a ready match. -/
theorem install_covers [DecidableEq Wait] {table : JoinIndex Ch Wait}
    {channels : Wait → List Ch} {live : Finset Wait}
    (before : table.Covers channels live) (waiter : Wait) (fresh : waiter ∉ live) :
    (table.install (channels waiter) waiter).Covers channels
      (insert waiter (live \ (table.installed (channels waiter)).toList.toFinset)) := by
  let keys := channels waiter
  let reached := table.install keys waiter
  have here : reached.waitersAt keys = waiter :: table.ordinary keys := by
    simp [reached, install, waitersAt]
  have away {ks : List Ch} (different : ks ≠ keys) :
      reached.waitersAt ks = table.waitersAt ks := by
    simp only [reached, install, waitersAt, Function.update_of_ne different]
  have localOrdinary : (table.ordinary keys).Nodup := (List.nodup_append.mp (before.unique keys)).2.1
  have apart (w : Wait) (inTable : w ∈ table.ordinary keys) :
      w ∉ (table.installed keys).toList :=
    fun also => (List.nodup_append.mp (before.unique keys)).2.2 w also w inTable rfl
  have members (ks : List Ch) (w : Wait) :
      w ∈ reached.waitersAt ks ↔ (w ∈ table.waitersAt ks ∧ w ∉ (table.installed keys).toList) ∨
        (w = waiter ∧ keys = ks) := by
    by_cases same : ks = keys
    · subst ks
      rw [here]
      constructor
      · intro member
        rcases List.mem_cons.mp member with rfl | ordinary
        · exact .inr ⟨rfl, rfl⟩
        · exact .inl ⟨List.mem_append.mpr (.inr ordinary), apart w ordinary⟩
      · rintro (⟨old, separate⟩ | ⟨rfl, _⟩)
        · exact List.mem_cons_of_mem _ ((List.mem_append.mp old).resolve_left separate)
        · exact List.mem_cons_self
    · rw [away same]
      constructor
      · intro old
        refine .inl ⟨old, ?_⟩
        intro replaced
        have otherKey := ((before.bucket ks w).mp old).2
        have thisKey := ((before.bucket keys w).mp (List.mem_append.mpr (.inl replaced))).2
        exact same (otherKey.symm.trans thisKey)
      · rintro (⟨old, _⟩ | ⟨_, equal⟩)
        · exact old
        · exact (same equal.symm).elim
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ks w
    rw [members, before.bucket, Finset.mem_insert, Finset.mem_sdiff, List.mem_toFinset]
    constructor
    · rintro (⟨⟨old, atKey⟩, preserved⟩ | ⟨rfl, atKey⟩)
      · exact ⟨.inr ⟨old, preserved⟩, atKey⟩
      · exact ⟨.inl rfl, atKey⟩
    · rintro ⟨rfl | ⟨old, preserved⟩, atKey⟩
      · exact .inr ⟨rfl, atKey⟩
      · exact .inl ⟨⟨old, atKey⟩, preserved⟩
  · intro ks
    by_cases same : ks = keys
    · subst ks
      rw [here]
      exact List.nodup_cons.mpr ⟨fun old => fresh ((before.bucket keys waiter).mp
        (List.mem_append.mpr (.inr old))).1, localOrdinary⟩
    · rw [away same]
      exact before.unique ks
  · intro ch ks member
    rcases (install_keys_iff table keys waiter ch ks).mp member with old | ⟨rfl, onKey⟩
    · exact before.routed ch ks old
    · exact onKey
  · intro ch ks onKey witnesses
    apply (install_keys_iff table keys waiter ch ks).mpr
    by_cases same : ks = keys
    · exact .inr ⟨same, same ▸ onKey⟩
    · rw [away same] at witnesses
      exact .inl (before.covered ch ks onKey witnesses)

end JoinIndex

/-- The post-application reducer has one dispatch with its actual body
scope, possibly an active re-consume, and zero or more raw produces.
Even a peek with no reposts uses the joined return path, not the direct
dispatch path. -/
structure DispatchBatch (Start Request Offer : Type*) where
  dispatch : Start
  reconsume : Option Request
  produces : List Offer
  joined : Bool
  deriving DecidableEq

namespace DispatchBatch

/-- Future launch order; not an assertion about effect or completion order. -/
def jobs {Start Request Offer : Type*} (batch : DispatchBatch Start Request Offer) :
    List (Start ⊕ (Request ⊕ Offer)) :=
  .inl batch.dispatch :: (batch.reconsume.toList.map (Sum.inr ∘ Sum.inl) ++
    batch.produces.map (Sum.inr ∘ Sum.inr))

/-- The joined return ignores successful dispatch tags. Abort takes
precedence over exhaustion, then the ordinary errors retain launch
order and multiplicity as in the interpreter's aggregate. -/
def aggregate {Fault Result : Type*} [DecidableEq Fault]
    (skip : Result) (abort exhausted : Fault) (many : List Fault → Fault)
    (ordered : List (Except Fault Result)) : Except Fault Result :=
  let errors := ordered.filterMap fun value => match value with
    | .ok _ => none
    | .error fault => some fault
  if abort ∈ errors then .error abort else if exhausted ∈ errors then .error exhausted else
    match errors with
    | [] => .ok skip
    | [fault] => .error fault
    | _ => .error (many errors)

/-- The reducer observes a positional slot for each launched job. A
ready error is a completed slot, not a reason to cancel unfinished jobs.
The direct dispatch case reads the body slot without aggregation. -/
def report {Start Request Offer Fault Result : Type*} [DecidableEq Fault]
    (batch : DispatchBatch Start Request Offer)
    (skip : Result) (abort exhausted : Fault) (many : List Fault → Fault)
    (slots : Fin batch.jobs.length → Option (Except Fault Result)) : Option (Except Fault Result) :=
  if batch.joined then
    ((List.ofFn slots).mapM id).map (aggregate skip abort exhausted many)
  else
    slots ⟨0, by simp [jobs]⟩

private theorem slot_sequence_iff {A : Type*} (slots : List (Option A)) (values : List A) :
    slots.mapM id = some values ↔ slots = values.map some := by
  induction slots generalizing values with
  | nil => cases values <;> simp
  | cons slot slots ih =>
    cases slot with
    | none => cases values <;> simp [List.mapM_cons, Bind.bind, Option.bind]
    | some val =>
      cases collected : slots.mapM id with
      | none =>
        have notReady (vals : List A) : slots ≠ vals.map some := by
          intro eq
          have := (ih vals).mpr eq
          simp [collected] at this
        cases values <;> simp [List.mapM_cons, Bind.bind, Option.bind, collected, notReady]
      | some vals =>
        cases values with
        | nil => simp [List.mapM_cons, Bind.bind, Option.bind, Pure.pure, collected]
        | cons head tail =>
          have assoc : slots = tail.map some ↔ vals = tail := by
            rw [← ih tail, collected, Option.some.injEq]
          simp [List.mapM_cons, Bind.bind, Option.bind, Pure.pure, collected, assoc]

/-- Both directions of the join barrier. In particular a slot that has
not returned prevents a report even if another returned a fatal error. -/
theorem joined_report_iff {Start Request Offer Fault Result : Type*} [DecidableEq Fault]
    (batch : DispatchBatch Start Request Offer)
    (skip : Result) (abort exhausted : Fault) (many : List Fault → Fault)
    (slots : Fin batch.jobs.length → Option (Except Fault Result)) (outcome : Except Fault Result)
    (joined : batch.joined = true) :
    report batch skip abort exhausted many slots = some outcome ↔
      ∃ values : List (Except Fault Result), List.ofFn slots = values.map some ∧
        aggregate skip abort exhausted many values = outcome := by
  simp only [report, joined, if_true, Option.map_eq_some_iff, slot_sequence_iff]

/-- Writing results of distinct workers in the other order changes
neither their positions nor what the parent can report afterwards.
This does not exchange their shared-store effects. -/
theorem report_swap_recording {Start Request Offer Fault Result : Type*} [DecidableEq Fault]
    (batch : DispatchBatch Start Request Offer)
    (skip : Result) (abort exhausted : Fault) (many : List Fault → Fault)
    (slots : Fin batch.jobs.length → Option (Except Fault Result))
    {i j : Fin batch.jobs.length} (apart : i ≠ j) (first second : Except Fault Result) :
    report batch skip abort exhausted many (Function.update (Function.update slots i (some first)) j (some second)) =
      report batch skip abort exhausted many (Function.update (Function.update slots j (some second)) i (some first)) := by
  rw [Function.update_comm apart]

end DispatchBatch

def prepareProduceBatch {Body Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (body : Body) (receiverSeed : Supply)
    (offer : ProduceRequest Ch Val) (peek : Bool) (binds : List (Ch × Pat))
    (selected : List (Match Val Arg)) :
    Option (DispatchBatch (Body × EvalScope Arg Supply) Empty (ProduceRequest Ch Val)) :=
  (processDispatch randomOf merge body receiverSeed selected).map fun invocation =>
    ⟨invocation, none, afterProduce offer peek binds selected, offer.2.2 || peek⟩

def prepareConsumeBatch {Body Supply Request : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (body : Body) (receiverSeed : Supply)
    (request : Request) (persistent peek : Bool) (binds : List (Ch × Pat)) (selected : List (Match Val Arg)) :
    Option (DispatchBatch (Body × EvalScope Arg Supply) Request (ProduceRequest Ch Val)) :=
  let (again, reposts) := afterConsume request persistent peek binds selected
  (processDispatch randomOf merge body receiverSeed selected).map fun invocation =>
    ⟨invocation, again, reposts, persistent || peek⟩

section LockedOutcome

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-- The active receive has no old waiting occurrence to take or keep. -/
def activeConsumeCommit {Wait : Type*} (binds : List (Ch × Pat)) (selected : List (Match Val Arg)) :
    Commit ((Ch × Int) ⊕ Wait) Val :=
  let data := lockedDataCommit binds selected
  ⟨data.taken.disjSum ∅, data.kept.disjSum ∅, ∅, []⟩

private def lowerLocked {O Hit Work : Type*} (park : Commit O Val) (found : Option Hit)
    (launch : Hit → Option (Commit O Val × Work)) : Option (Commit O Val × Option Work) :=
  match found with
  | none => some (park, none)
  | some receipt => (launch receipt).map fun (commit, work) => (commit, some work)

private theorem lowerLocked_no_dispatch_iff {O Hit Work : Type*} {park commit : Commit O Val}
    {found : Option Hit} {launch : Hit → Option (Commit O Val × Work)} :
    lowerLocked park found launch = some (commit, none) ↔ found = none ∧ commit = park := by
  cases found with
  | none => simp [lowerLocked, eq_comm]
  | some selected => cases launch selected <;> simp [lowerLocked]

/-- One non-replay produce cut. A miss stores the offered datum and
has no post-lock dispatch. The supplied key names the new occurrence
for this cut; it is not a Rust array position in the next view. -/
def lockedProduce {Wait Body Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (binds : Wait → List (Ch × Pat))
    (continuation : Wait → Body × Supply) (persistent peek : Wait → Bool)
    (offer : ProduceRequest Ch Val) (groups : List (WaitView Ch Val Wait)) (freshKey : Int) :
    Option (Commit ((Ch × Int) ⊕ Wait) Val × Option
      (DispatchBatch (Body × EvalScope Arg Supply) Empty (ProduceRequest Ch Val))) :=
  lowerLocked (Commit.makeOne (.inl (offer.1, freshKey))) (offerSearch capture binds offer groups)
    fun (waiter, selected) =>
      (prepareProduceBatch randomOf merge (continuation waiter).1 (continuation waiter).2 offer
        (peek waiter) (binds waiter) selected).map fun work =>
          (parkedProduceCommit (binds waiter) selected waiter (persistent waiter), work)

private def consumeWithPark {Wait Body Supply Request : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (body : Body) (seed : Supply)
    (request : Request) (persistent peek : Bool) (binds : List (Ch × Pat))
    (cache : Ch → List (Datum Val)) (park : Commit ((Ch × Int) ⊕ Wait) Val) :
    Option (Commit ((Ch × Int) ⊕ Wait) Val × Option
      (DispatchBatch (Body × EvalScope Arg Supply) Request (ProduceRequest Ch Val))) :=
  lowerLocked park (packet capture binds cache) fun selected =>
    (prepareConsumeBatch randomOf merge body seed request persistent peek binds selected).map
      fun work => (activeConsumeCommit binds selected, work)

/-- Consume with fresh-only registration. The native index can
additionally license reusing a parked duplicate, below. On a hit
registration is irrelevant and the selected data packet dispatches. -/
def lockedConsume {Wait Body Supply Request : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (body : Body) (seed : Supply)
    (request : Request) (persistent peek : Bool) (binds : List (Ch × Pat))
    (cache : Ch → List (Datum Val)) (freshWaiter : Wait) :
    Option (Commit ((Ch × Int) ⊕ Wait) Val × Option
      (DispatchBatch (Body × EvalScope Arg Supply) Request (ProduceRequest Ch Val))) :=
  consumeWithPark capture randomOf merge body seed request persistent peek binds cache
    (Commit.makeOne (.inr freshWaiter))

theorem locked_produce_no_dispatch_iff {Wait Body Supply : Type*} (randomOf : Val → Supply)
    (merge : Supply → Supply → List Supply → Supply) (binds : Wait → List (Ch × Pat))
    (continuation : Wait → Body × Supply) (persistent peek : Wait → Bool)
    (offer : ProduceRequest Ch Val) (groups : List (WaitView Ch Val Wait)) (freshKey : Int)
    (commit : Commit ((Ch × Int) ⊕ Wait) Val) :
    lockedProduce capture randomOf merge binds continuation persistent peek offer groups freshKey =
      some (commit, none) ↔
    offerSearch capture binds offer groups = none ∧ commit = Commit.makeOne (.inl (offer.1, freshKey)) :=
  lowerLocked_no_dispatch_iff

theorem locked_consume_no_dispatch_iff {Wait Body Supply Request : Type*}
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply) (body : Body) (seed : Supply)
    (request : Request) (persistent peek : Bool) (binds : List (Ch × Pat))
    (cache : Ch → List (Datum Val)) (freshWaiter : Wait) (commit : Commit ((Ch × Int) ⊕ Wait) Val) :
    lockedConsume capture randomOf merge body seed request persistent peek binds cache freshWaiter =
      some (commit, none) ↔
    packet capture binds cache = none ∧ commit = Commit.makeOne (.inr freshWaiter) :=
  lowerLocked_no_dispatch_iff

private theorem fresh_make_admitted {O R : Type*} [DecidableEq O] (label : O → R)
    {store : Finset O} {key : O} (fresh : key ∉ store) : Enabled label store (Commit.makeOne key) := by
  refine ⟨Finset.empty_subset _, Finset.empty_subset _, Finset.disjoint_empty_left _, ?_, ?_⟩
  · simpa using fresh
  · intro query found
    simp at found

/-- Interpret readiness on the actual finite occurrence cut. Distinct
keys carrying equal values still represent distinct data occurrences. -/
def StoredValue (live : Finset (Ch × Int)) (label : Ch × Int → Val) (channel : Ch) (value : Val) : Prop :=
  ∃ index : Int, (channel, index) ∈ live ∧ label (channel, index) = value

/-- All installed waiters are blocked on the current fixed data cut.
This property is about ready matches, not scheduler fairness. -/
def ParkedQuiet {Wait : Type*} (binds : Wait → List (Ch × Pat))
    (waiters : Finset Wait) (live : Finset (Ch × Int)) (label : Ch × Int → Val) : Prop :=
  ∀ waiter ∈ waiters, ¬ ReadyOn capture (StoredValue live label) (binds waiter)

omit [DecidableEq Ch] in
theorem ParkedQuiet.shrink {Wait : Type*} {binds : Wait → List (Ch × Pat)}
    {waiters waiters' : Finset Wait} {live live' : Finset (Ch × Int)} {label : Ch × Int → Val}
    (quiet : ParkedQuiet capture binds waiters live label)
    (waiting : waiters' ⊆ waiters) (data : live' ⊆ live) :
    ParkedQuiet capture binds waiters' live' label := by
  intro waiter parked ready
  apply quiet waiter (waiting parked)
  intro bind member
  obtain ⟨raw, ⟨i, available, reads⟩, matched⟩ := ready bind member
  exact ⟨raw, ⟨i, data available, reads⟩, matched⟩

theorem stored_value_insert {live : Finset (Ch × Int)} {label : Ch × Int → Val}
    (offer : ProduceRequest Ch Val) (key : Int) (value : label (offer.1, key) = offer.2.1)
    (channel : Ch) (raw : Val) :
    StoredValue (insert (offer.1, key) live) label channel raw ↔
      offeredValues (StoredValue live label) offer channel raw := by
  constructor
  · rintro ⟨index, present, reads⟩
    rcases Finset.mem_insert.mp present with placed | earlier
    · obtain ⟨same, index'⟩ := Prod.mk.inj placed
      rw [same, index', value] at reads
      exact .inr ⟨same, reads.symm⟩
    · exact .inl ⟨index, earlier, reads⟩
  · rintro (⟨index, present, reads⟩ | ⟨rfl, rfl⟩)
    · exact ⟨index, Finset.mem_insert_of_mem present, reads⟩
    · exact ⟨key, Finset.mem_insert_self _ _, value⟩

/-- The unshuffled array presented by `put_datum`. Array indices are
coordinates of the current view, not enduring occurrence identities.
The next native shuffle is still a separate input to preparation. -/
def putDatumView (arrays : Ch → List (Datum Val)) (offer : ProduceRequest Ch Val) :
    Ch → List (Datum Val) :=
  Function.update arrays offer.1 (⟨offer.2.1, 0, offer.2.2⟩ ::
    (arrays offer.1).map (fun row => {row with index := row.index + 1}))

theorem put_datum_view_slots (arrays : Ch → List (Datum Val)) (offer : ProduceRequest Ch Val) :
    (putDatumView arrays offer offer.1)[0]? = some ⟨offer.2.1, 0, offer.2.2⟩ ∧
    (∀ i, (putDatumView arrays offer offer.1)[i + 1]? =
      ((arrays offer.1)[i]?).map (fun row => {row with index := row.index + 1})) ∧
    (∀ ch, ch ≠ offer.1 → putDatumView arrays offer ch = arrays ch) := by
  refine ⟨by simp [putDatumView], ?_, ?_⟩
  · intro i
    rw [putDatumView, Function.update_self, List.getElem?_cons_succ, List.getElem?_map]
  · intro ch other
    rw [putDatumView, Function.update_of_ne other]

def slotAfterPut (channel : Ch) (freshKey : Int) (key : Ch × Int) : Ch × Int :=
  (key.1, if key.1 = channel then
    (if key.2 = freshKey then 0 else key.2 + 1) else key.2)

/-- Re-chart the made key at native slot zero and all older keys on
that channel one place later. No two live occurrences are identified,
even when their labels and flags agree. -/
theorem slot_after_put_injective (live : Finset (Ch × Int)) (channel : Ch) (freshKey : Int)
    (indices : ∀ key ∈ live, 0 ≤ key.2) :
    Set.InjOn (slotAfterPut channel freshKey) (↑(insert (channel, freshKey) live) : Set (Ch × Int)) := by
  rintro ⟨source, first⟩ earlier ⟨target, later⟩ recent equal
  have sameChannel : source = target := congrArg Prod.fst equal
  subst target
  apply congrArg (fun i : Int => (source, i))
  by_cases changed : source = channel
  · subst source
    have sameSlot : (if first = freshKey then (0 : Int) else first + 1) =
        (if later = freshKey then 0 else later + 1) := by
      simpa only [slotAfterPut, if_true, Prod.fst, Prod.snd] using congrArg Prod.snd equal
    by_cases left : first = freshKey
    · by_cases right : later = freshKey
      · exact left.trans right.symm
      · have old : (channel, later) ∈ live :=
          (Finset.mem_insert.mp recent).resolve_left (fun same => right (Prod.mk.inj same).2)
        have positive := indices _ old
        simp only [if_pos left, if_neg right] at sameSlot
        omega
    · by_cases right : later = freshKey
      · have old : (channel, first) ∈ live :=
          (Finset.mem_insert.mp earlier).resolve_left (fun same => left (Prod.mk.inj same).2)
        have positive := indices _ old
        simp only [if_neg left, if_pos right] at sameSlot
        omega
      · simp only [if_neg left, if_neg right] at sameSlot
        omega
  · simpa only [slotAfterPut, if_neg changed, Prod.fst, Prod.snd] using congrArg Prod.snd equal

/-- Storing the datum and re-indexing the array does not change the
value view used to certify that the offer was a miss. -/
theorem put_datum_view_covers {arrays : Ch → List (Datum Val)}
    {live : Finset (Ch × Int)} {label : Ch × Int → Val}
    (offer : ProduceRequest Ch Val) (key : Int) (labelled : label (offer.1, key) = offer.2.1)
    {channel : Ch} (covered : ViewValues arrays (StoredValue live label) channel) :
    ViewValues (putDatumView arrays offer) (StoredValue (insert (offer.1, key) live) label) channel := by
  intro raw
  rw [stored_value_insert offer key labelled]
  by_cases atOffer : channel = offer.1
  · subst channel
    constructor
    · rintro ⟨row, seen, rfl⟩
      rw [putDatumView, Function.update_self, List.mem_cons] at seen
      rcases seen with rfl | fromOld
      · exact .inr ⟨rfl, rfl⟩
      · obtain ⟨old, present, rfl⟩ := List.mem_map.mp fromOld
        exact .inl ((covered _).mp ⟨old, present, rfl⟩)
    · rintro (old | ⟨_, rfl⟩)
      · obtain ⟨row, present, rfl⟩ := (covered raw).mpr old
        refine ⟨{row with index := row.index + 1}, ?_, rfl⟩
        rw [putDatumView, Function.update_self]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, present, rfl⟩)
      · exact ⟨⟨offer.2.1, 0, offer.2.2⟩, by simp [putDatumView], rfl⟩
  · simpa only [putDatumView, Function.update_of_ne atOffer, offeredValues, atOffer,
      false_and, or_false] using covered raw

/-- Parking a request is an admitted single occurrence make.
Completeness of the data view rules out a secretly ready new waiter. -/
theorem consume_miss_parks {Wait : Type*} [DecidableEq Wait] (binds : Wait → List (Ch × Pat))
    (waiter : Wait) (waitingLabel : Wait → Val) (live : Finset (Ch × Int)) (waiters : Finset Wait)
    (dataLabel : Ch × Int → Val) (cache : Ch → List (Datum Val))
    (indexed : ((binds waiter).map Prod.fst).Nodup)
    (covered : ∀ bind ∈ binds waiter, ViewValues cache (StoredValue live dataLabel) bind.1)
    (missed : packet capture (binds waiter) cache = none) (fresh : waiter ∉ waiters)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    let cut : Commit ((Ch × Int) ⊕ Wait) Val := Commit.makeOne (.inr waiter)
    Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      fire (live.disjSum waiters) cut = live.disjSum (insert waiter waiters) ∧
      ParkedQuiet capture binds (insert waiter waiters) live dataLabel := by
  refine ⟨fresh_make_admitted _ (by simpa using fresh), ?_, ?_⟩
  · ext id
    cases id <;> simp [fire]
  · intro w present
    rcases Finset.mem_insert.mp present with rfl | earlier
    · exact (packet_none_iff_not_readyOn capture indexed covered).mp missed
    · exact quiet w earlier

/-- A produce miss inserts exactly one datum and retains all waiters.
Only a waiter using the offered channel could gain readiness from the
insert. The complete join lookup excludes every such wake-up. -/
theorem produce_miss_stores {Wait : Type*} [DecidableEq Wait] (binds : Wait → List (Ch × Pat))
    (offer : ProduceRequest Ch Val) (groups : List (WaitView Ch Val Wait))
    (waitingLabel : Wait → Val) (live : Finset (Ch × Int)) (waiters : Finset Wait)
    (dataLabel : Ch × Int → Val) (key : Int)
    (index : ∀ w, (w ∈ waiters ∧ offer.1 ∈ (binds w).map Prod.fst) ↔
      ∃ group ∈ groups, w ∈ group.2)
    (distinct : ∀ w ∈ waiters, ((binds w).map Prod.fst).Nodup)
    (covered : ∀ group ∈ groups, ∀ w ∈ group.2, ∀ bind ∈ binds w,
      ViewValues group.1 (StoredValue live dataLabel) bind.1)
    (missed : offerSearch capture binds offer groups = none)
    (fresh : (offer.1, key) ∉ live) (labelled : dataLabel (offer.1, key) = offer.2.1)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    let cut : Commit ((Ch × Int) ⊕ Wait) Val := Commit.makeOne (.inl (offer.1, key))
    Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      fire (live.disjSum waiters) cut = (insert (offer.1, key) live).disjSum waiters ∧
      ParkedQuiet capture binds waiters (insert (offer.1, key) live) dataLabel := by
  refine ⟨fresh_make_admitted _ (by simpa using fresh), ?_, ?_⟩
  · ext id
    cases id <;> simp [fire]
  · intro w installed ready
    have all : ReadyOn capture (offeredValues (StoredValue live dataLabel) offer) (binds w) := by
      intro slot member
      obtain ⟨value, visible, captured⟩ := ready slot member
      exact ⟨value, (stored_value_insert offer key labelled slot.1 value).mp visible, captured⟩
    by_cases watches : offer.1 ∈ (binds w).map Prod.fst
    · exact (offer_search_none_iff_no_wake capture binds offer groups waiters
        (StoredValue live dataLabel) index distinct covered).mp missed w installed watches all
    · apply quiet w installed
      intro slot member
      obtain ⟨value, visible, captured⟩ := all slot member
      rcases visible with old | ⟨same, _⟩
      · exact ⟨value, old, captured⟩
      · exact (watches (same ▸ List.mem_map_of_mem (f := Prod.fst) member)).elim

private theorem active_consume_admitted {Wait : Type*} {binds : List (Ch × Pat)}
    {selected : List (Match Val Arg)} {live : Finset (Ch × Int)} {dataLabel : Ch × Int → Val}
    (waiters : Finset Wait) (waitingLabel : Wait → Val)
    (data : Enabled dataLabel live (lockedDataCommit binds selected)) :
    Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters)
      (activeConsumeCommit binds selected) := by
  refine ⟨Finset.disjSum_mono data.taken_subset (Finset.empty_subset _),
    Finset.disjSum_mono data.kept_subset (Finset.empty_subset _), ?_, Finset.disjoint_empty_left _, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro id taken kept
    cases id with
    | inl key =>
      exact Finset.disjoint_left.mp data.apart
        (Finset.inl_mem_disjSum.mp taken) (Finset.inl_mem_disjSum.mp kept)
    | inr key =>
      have impossible : key ∈ (∅ : Finset Wait) := Finset.inr_mem_disjSum.mp taken
      simp at impossible
  · intro query impossible
    cases impossible

private theorem active_consume_projects {Wait : Type*} [DecidableEq Wait] (binds : List (Ch × Pat))
    (selected : List (Match Val Arg)) (live : Finset (Ch × Int)) (waiters : Finset Wait) :
    fire (live.disjSum waiters) (activeConsumeCommit binds selected) =
      (fire live (lockedDataCommit binds selected)).disjSum waiters := by
  ext key
  cases key <;> simp [fire, activeConsumeCommit, lockedDataCommit]

private theorem consume_with_park_refines {Wait Body Supply Request : Type*} [DecidableEq Wait]
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply) (body : Body) (seed : Supply)
    (request : Request) (persistent peek : Bool) (binds : Wait → List (Ch × Pat))
    (cache : Ch → List (Datum Val)) (waiter : Wait) (park : Commit ((Ch × Int) ⊕ Wait) Val)
    (live : Finset (Ch × Int)) (waiters : Finset Wait) (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (nonempty : binds waiter ≠ []) (distinct : ((binds waiter).map Prod.fst).Nodup)
    (covered : ∀ slot ∈ binds waiter, ViewValues cache (StoredValue live dataLabel) slot.1)
    (present : ∀ source datum, datum ∈ cache source → (source, datum.index) ∈ live)
    (indexed : ∀ source a b, a ∈ cache source → b ∈ cache source → a.index = b.index → a = b)
    (canPark : packet capture (binds waiter) cache = none →
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) park ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) park).toRight
        (fire (live.disjSum waiters) park).toLeft dataLabel)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    ∃ cut work, consumeWithPark capture randomOf merge body seed request persistent peek (binds waiter) cache park =
        some (cut, work) ∧
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) cut).toRight
        (fire (live.disjSum waiters) cut).toLeft dataLabel ∧
      (work = none ↔ ¬ ReadyOn capture (StoredValue live dataLabel) (binds waiter)) ∧
      (fire (live.disjSum waiters) cut).toRight =
        (if work.isNone then (fire (live.disjSum waiters) park).toRight else waiters) := by
  have readiness := packet_none_iff_not_readyOn capture distinct covered
  cases found : packet capture (binds waiter) cache with
  | none =>
    obtain ⟨admitted, stays⟩ := canPark found
    exact ⟨park, none, by simp [consumeWithPark, lowerLocked, found], admitted, stays,
      ⟨fun _ => readiness.mp found, fun _ => rfl⟩, rfl⟩
  | some selected =>
    have ready := (packet_isSome_iff_readyOn capture distinct covered).mp (by rw [found]; rfl)
    have data := locked_data_admitted capture live dataLabel present indexed (fun _ _ inView _ => inView) found
    have admitted := active_consume_admitted waiters waitingLabel data
    have projected := active_consume_projects (binds waiter) selected live waiters
    have shrinks : fire live (lockedDataCommit (binds waiter) selected) ⊆ live := by
      simp [fire, lockedDataCommit]
    have start : ∃ work, prepareConsumeBatch randomOf merge body seed request persistent peek
        (binds waiter) selected = some work := by
      cases layout : binds waiter with
      | nil => exact (nonempty layout).elim
      | cons first more =>
        rw [layout] at found
        obtain ⟨scope, opens, _⟩ := process_dispatch_of_packet capture randomOf merge body seed first more cache found
        let follow := afterConsume request persistent peek (first :: more) selected
        exact ⟨⟨(body, scope), follow.1, follow.2, persistent || peek⟩,
          by simp [prepareConsumeBatch, opens, follow]⟩
    obtain ⟨work, starts⟩ := start
    refine ⟨_, some work, by simp [consumeWithPark, lowerLocked, found, starts], admitted, ?_, ?_, ?_⟩
    · simpa only [projected, Finset.toRight_disjSum, Finset.toLeft_disjSum] using
        (ParkedQuiet.shrink capture quiet (Finset.Subset.refl _) shrinks)
    · simp [ready]
    · rw [projected, Finset.toRight_disjSum]
      rfl

/-- Both possible outcomes of a prepared active receive are admitted
with fresh-only registration at misses. Native idempotent parking
uses the same data and dispatch proof. -/
theorem locked_consume_refines_cut {Wait Body Supply Request : Type*} [DecidableEq Wait]
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply) (body : Body) (seed : Supply)
    (request : Request) (persistent peek : Bool) (binds : Wait → List (Ch × Pat))
    (cache : Ch → List (Datum Val)) (waiter : Wait)
    (live : Finset (Ch × Int)) (waiters : Finset Wait) (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (nonempty : binds waiter ≠ []) (distinct : ((binds waiter).map Prod.fst).Nodup)
    (covered : ∀ slot ∈ binds waiter, ViewValues cache (StoredValue live dataLabel) slot.1)
    (present : ∀ source datum, datum ∈ cache source → (source, datum.index) ∈ live)
    (indexed : ∀ source a b, a ∈ cache source → b ∈ cache source → a.index = b.index → a = b)
    (fresh : packet capture (binds waiter) cache = none → waiter ∉ waiters)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    ∃ cut work, lockedConsume capture randomOf merge body seed request persistent peek (binds waiter) cache waiter =
        some (cut, work) ∧
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) cut).toRight
        (fire (live.disjSum waiters) cut).toLeft dataLabel ∧
      (work = none ↔ ¬ ReadyOn capture (StoredValue live dataLabel) (binds waiter)) := by
  let park : Commit ((Ch × Int) ⊕ Wait) Val := Commit.makeOne (.inr waiter)
  have canPark (missed : packet capture (binds waiter) cache = none) :
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) park ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) park).toRight
        (fire (live.disjSum waiters) park).toLeft dataLabel := by
    obtain ⟨admitted, reached, stays⟩ := consume_miss_parks capture binds waiter waitingLabel
      live waiters dataLabel cache distinct covered missed (fresh missed) quiet
    refine ⟨admitted, ?_⟩
    simpa only [park, reached, Finset.toRight_disjSum, Finset.toLeft_disjSum] using stays
  obtain ⟨cut, work, run, admitted, stays, exactMiss, _⟩ :=
    consume_with_park_refines capture randomOf merge body seed request persistent peek binds cache
      waiter park live waiters dataLabel waitingLabel nonempty distinct covered present indexed canPark quiet
  exact ⟨cut, work, run, admitted, stays, exactMiss⟩

namespace JoinIndex

/-- An ordinary duplicate keeps the existing occurrence. Only a
genuinely new identity requires a fresh occurrence allocation. -/
def parkCommit {Wait Identity : Type*} [DecidableEq Identity]
    (table : JoinIndex Ch Wait) (identity : Wait → Identity) (keys : List Ch) (waiter : Wait) :
    Commit ((Ch × Int) ⊕ Wait) Val :=
  match table.duplicate identity keys waiter with
  | none => Commit.makeOne (.inr waiter)
  | some old => Commit.keepOne (.inr old)

theorem park_commit_refines {Wait Identity : Type*} [DecidableEq Identity] [DecidableEq Wait]
    {table : JoinIndex Ch Wait} {channels : Wait → List Ch} {waiters : Finset Wait}
    (before : table.Covers channels waiters) (identity : Wait → Identity) (waiter : Wait)
    (live : Finset (Ch × Int)) (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (fresh : table.duplicate identity (channels waiter) waiter = none → waiter ∉ waiters) :
    let cut := table.parkCommit (Val := Val) identity (channels waiter) waiter
    ∃ next : Finset Wait,
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      fire (live.disjSum waiters) cut = live.disjSum next ∧
      (table.park identity (channels waiter) waiter).Covers channels next ∧
      ∀ w ∈ next, w ∈ waiters ∨ w = waiter := by
  dsimp only
  have after := table.park_covers before identity waiter fresh
  cases found : table.duplicate identity (channels waiter) waiter with
  | none =>
    have unused := fresh found
    rw [parkCommit, found]
    refine ⟨insert waiter waiters, fresh_make_admitted _ (by simpa using unused), ?_, ?_, ?_⟩
    · ext key
      cases key <;> simp [fire]
    · simpa only [found] using after
    · intro w recent
      exact (Finset.mem_insert.mp recent).symm
  | some earlier =>
    have ordinary : earlier ∈ table.ordinary (channels waiter) := List.mem_of_find?_eq_some found
    have member : earlier ∈ waiters := ((before.bucket (channels waiter) earlier).mp
      (List.mem_append.mpr (.inr ordinary))).1
    rw [parkCommit, found]
    refine ⟨waiters, ?_, by simp [fire], ?_, fun w recent => .inl recent⟩
    · refine ⟨Finset.empty_subset _, ?_, Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, ?_⟩
      · simpa using member
      · intro query notMem
        simp at notMem
    · simpa only [found] using after

end JoinIndex

/-- Native consume consults the ordinary bucket only on a miss; the
match and dispatch algorithm is the same as the fresh-only profile. -/
def lockedIndexedConsume {Wait Body Supply Request Identity : Type*} [DecidableEq Identity]
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply) (body : Body) (seed : Supply)
    (request : Request) (persistent peek : Bool) (binds : Wait → List (Ch × Pat))
    (cache : Ch → List (Datum Val)) (waiter : Wait) (table : JoinIndex Ch Wait) (identity : Wait → Identity) :
    Option (Commit ((Ch × Int) ⊕ Wait) Val × Option
      (DispatchBatch (Body × EvalScope Arg Supply) Request (ProduceRequest Ch Val))) :=
  consumeWithPark capture randomOf merge body seed request persistent peek (binds waiter) cache
    (table.parkCommit identity ((binds waiter).map Prod.fst) waiter)

/-- Consume with the maintained RSpace index: both the duplicate
and fresh miss branches, as well as a successful active receive,
leave a covered and quiet next lock cut. -/
theorem indexed_consume_refines_cut {Wait Body Supply Request Identity : Type*} [DecidableEq Wait]
    [DecidableEq Identity] (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply)
    (body : Body) (seed : Supply) (request : Request) (persistent peek : Bool)
    (binds : Wait → List (Ch × Pat)) (cache : Ch → List (Datum Val)) (waiter : Wait)
    (table : JoinIndex Ch Wait) (identity : Wait → Identity)
    (live : Finset (Ch × Int)) (waiters : Finset Wait) (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (nonempty : binds waiter ≠ []) (distinct : ((binds waiter).map Prod.fst).Nodup)
    (covered : ∀ slot ∈ binds waiter, ViewValues cache (StoredValue live dataLabel) slot.1)
    (present : ∀ source datum, datum ∈ cache source → (source, datum.index) ∈ live)
    (indexed : ∀ source a b, a ∈ cache source → b ∈ cache source → a.index = b.index → a = b)
    (roster : table.Covers (fun w => (binds w).map Prod.fst) waiters)
    (fresh : packet capture (binds waiter) cache = none →
      table.duplicate identity ((binds waiter).map Prod.fst) waiter = none → waiter ∉ waiters)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    ∃ cut work, lockedIndexedConsume capture randomOf merge body seed request persistent peek binds cache
        waiter table identity = some (cut, work) ∧
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) cut).toRight
        (fire (live.disjSum waiters) cut).toLeft dataLabel ∧
      (work = none ↔ ¬ ReadyOn capture (StoredValue live dataLabel) (binds waiter)) ∧
      (if work.isNone then table.park identity ((binds waiter).map Prod.fst) waiter else table).Covers
        (fun w => (binds w).map Prod.fst) (fire (live.disjSum waiters) cut).toRight := by
  let keys := (binds waiter).map Prod.fst
  let park := table.parkCommit (Val := Val) identity keys waiter
  have exactMiss := packet_none_iff_not_readyOn capture distinct covered
  have certificate (missed : packet capture (binds waiter) cache = none) :
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) park ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) park).toRight
        (fire (live.disjSum waiters) park).toLeft dataLabel ∧
      (table.park identity keys waiter).Covers
        (fun w => (binds w).map Prod.fst) (fire (live.disjSum waiters) park).toRight := by
    obtain ⟨next, admissible, reached, ready, origins⟩ :=
      table.park_commit_refines roster identity waiter live dataLabel waitingLabel (fresh missed)
    refine ⟨admissible, ?_, ?_⟩
    · rw [reached, Finset.toRight_disjSum, Finset.toLeft_disjSum]
      intro w present
      rcases origins w present with prior | rfl
      · exact quiet w prior
      · exact exactMiss.mp missed
    · rwa [reached, Finset.toRight_disjSum]
  obtain ⟨cut, work, executed, admitted, stopped, miss, pending⟩ := consume_with_park_refines capture
    randomOf merge body seed request persistent peek binds cache waiter park live waiters
    dataLabel waitingLabel nonempty distinct covered present indexed
    (fun missed => ⟨(certificate missed).1, (certificate missed).2.1⟩) quiet
  refine ⟨cut, work, executed, admitted, stopped, miss, ?_⟩
  rw [pending]
  cases work with
  | none => exact (certificate (exactMiss.mpr (miss.mp rfl))).2.2
  | some work => exact roster

end LockedOutcome

section OfferHandoff

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-- The selected waiter, occurrence cut and scheduled work come from the
same successful packet. Installed receivers outside the cut remain live.
The prepared group views must represent the locked physical store. -/
theorem selected_offer_admits_and_dispatches {Wait Body Supply : Type*} [DecidableEq Wait]
    {binds : Wait → List (Ch × Pat)} {offer : ProduceRequest Ch Val}
    {groups : List (WaitView Ch Val Wait)} {waiting : Wait} {selected : List (Match Val Arg)}
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply)
    (continuation : Wait → Body × Supply) (persistent peek : Wait → Bool)
    (dataLive : Finset (Ch × Int)) (waiters : Finset Wait)
    (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (represented : ∀ group ∈ groups, ∀ source datum,
      datum ∈ group.1 source → (source, datum.index) ∈ dataLive ∧ dataLabel (source, datum.index) = datum.raw)
    (indexed : ∀ group ∈ groups, ∀ source a b,
      a ∈ group.1 source → b ∈ group.1 source → a.index = b.index → a = b)
    (registered : ∀ group ∈ groups, ∀ w ∈ group.2, w ∈ waiters)
    (nonempty : binds waiting ≠ [])
    (found : offerSearch capture binds offer groups = some (waiting, selected)) :
    let body := (continuation waiting).1
    let seed := (continuation waiting).2
    let commit := parkedProduceCommit (binds waiting) selected waiting (persistent waiting)
    Enabled (Sum.elim dataLabel waitingLabel) (dataLive.disjSum waiters) commit ∧
      (fire (dataLive.disjSum waiters) commit).toLeft = fire dataLive (lockedDataCommit (binds waiting) selected) ∧
      (fire (dataLive.disjSum waiters) commit).toRight =
        (if persistent waiting then waiters else waiters.erase waiting) ∧
      (∀ slot row, (slot, row) ∈ (binds waiting).zip selected → 0 ≤ row.datum.index →
        dataLabel (slot.1, row.datum.index) = row.datum.raw) ∧
      ∃ batch, prepareProduceBatch randomOf merge body seed offer (peek waiting) (binds waiting) selected =
          some batch ∧ batch.dispatch.1 = body ∧
        batch.produces = afterProduce offer (peek waiting) (binds waiting) selected ∧
        ∀ i, shiftedLookup batch.dispatch.2.stored batch.dispatch.2.shift i = (dispatchEnv selected)[i]? := by
  obtain ⟨before, group, after, layout, _, prior, later, ordered, _, delivered⟩ :=
    (offer_search_winner_iff capture).mp found
  have inside : group ∈ groups := by rw [layout]; simp
  have ready : waiting ∈ group.2 := by
    apply List.mem_reverse.mp
    rw [ordered]
    simp
  have dataReady := locked_data_admitted_with_offer capture dataLive dataLabel
    (fun source datum live => (represented group inside source datum live).1) (indexed group inside) delivered
  have admitted := parked_produce_admitted waitingLabel waiting (persistent waiting)
    (registered group inside waiting ready) dataReady
  have projected := parked_produce_projects (binds waiting) selected dataLive waiters waiting (persistent waiting)
  refine ⟨admitted, projected.1, projected.2, ?_, ?_⟩
  · intro slot row inPacket stored
    have inView := (paired_zip (packet_sound capture delivered) (slot, row) inPacket).1
    rcases mem_withOffer inView with old | ⟨_, incoming⟩
    · exact (represented group inside slot.1 row.datum old).2
    · rw [incoming] at stored
      change (0 : Int) ≤ -1 at stored
      omega
  let body := (continuation waiting).1
  let seed := (continuation waiting).2
  cases h : binds waiting with
  | nil => exact False.elim (nonempty h)
  | cons first tail =>
    rw [h] at delivered
    obtain ⟨scope, run, lookup⟩ := process_dispatch_of_packet capture randomOf merge body seed _ _ _ delivered
    refine ⟨⟨(body, scope), none, afterProduce offer (peek waiting) (first :: tail) selected,
      offer.2.2 || peek waiting⟩,
      ?_, rfl, rfl, lookup⟩
    change processDispatch randomOf merge (continuation waiting).1 (continuation waiting).2 selected =
      some (body, scope) at run
    simp [prepareProduceBatch, run, body]

/-- Exhaust the non-replay produce cut on a complete, fixed view. The
returned commit is admitted in either branch and preserves blockedness
of the installed waiters. Dispatch and reposts run only after this cut. -/
theorem locked_produce_refines_cut {Wait Body Supply : Type*} [DecidableEq Wait]
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply)
    (binds : Wait → List (Ch × Pat)) (continuation : Wait → Body × Supply) (persistent peek : Wait → Bool)
    (offer : ProduceRequest Ch Val) (groups : List (WaitView Ch Val Wait)) (key : Int)
    (live : Finset (Ch × Int)) (waiters : Finset Wait) (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (index : ∀ w, (w ∈ waiters ∧ offer.1 ∈ (binds w).map Prod.fst) ↔
      ∃ group ∈ groups, w ∈ group.2)
    (distinct : ∀ w ∈ waiters, ((binds w).map Prod.fst).Nodup)
    (covered : ∀ group ∈ groups, ∀ w ∈ group.2, ∀ slot ∈ binds w,
      ViewValues group.1 (StoredValue live dataLabel) slot.1)
    (represented : ∀ group ∈ groups, ∀ source datum,
      datum ∈ group.1 source → (source, datum.index) ∈ live ∧ dataLabel (source, datum.index) = datum.raw)
    (indexed : ∀ group ∈ groups, ∀ source a b,
      a ∈ group.1 source → b ∈ group.1 source → a.index = b.index → a = b)
    (fresh : offerSearch capture binds offer groups = none →
      (offer.1, key) ∉ live ∧ dataLabel (offer.1, key) = offer.2.1)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    ∃ cut work, lockedProduce capture randomOf merge binds continuation persistent peek offer groups key =
        some (cut, work) ∧
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) cut).toRight
        (fire (live.disjSum waiters) cut).toLeft dataLabel ∧
      (work = none ↔ ∀ w ∈ waiters, offer.1 ∈ (binds w).map Prod.fst →
        ¬ ReadyOn capture (offeredValues (StoredValue live dataLabel) offer) (binds w)) := by
  cases found : offerSearch capture binds offer groups with
  | none =>
    obtain ⟨unused, makesValue⟩ := fresh found
    obtain ⟨admitted, reached, stays⟩ := produce_miss_stores capture binds offer groups waitingLabel
      live waiters dataLabel key index distinct covered found unused makesValue quiet
    refine ⟨Commit.makeOne (.inl (offer.1, key)), none, by simp [lockedProduce, lowerLocked, found],
      admitted, ?_, ?_⟩
    · simpa only [reached, Finset.toRight_disjSum, Finset.toLeft_disjSum] using stays
    · exact ⟨fun _ => (offer_search_none_iff_no_wake capture binds offer groups waiters
        (StoredValue live dataLabel) index distinct covered).mp found, fun _ => rfl⟩
  | some pair =>
    obtain ⟨waiting, selected⟩ := pair
    obtain ⟨_, group, _, layout, _, _, _, ordered, _, _⟩ := (offer_search_winner_iff capture).mp found
    have groupLive : group ∈ groups := by rw [layout]; simp
    have readyInGroup : waiting ∈ group.2 := by apply List.mem_reverse.mp; rw [ordered]; simp
    have touches := ((index waiting).mpr ⟨group, groupLive, readyInGroup⟩).2
    have nonempty : binds waiting ≠ [] := by intro empty; simp [empty] at touches
    obtain ⟨admitted, dataCut, waitCut, _, work, opens, _, _, _⟩ :=
      selected_offer_admits_and_dispatches capture randomOf merge continuation persistent peek
        live waiters dataLabel waitingLabel represented
        (indexed := indexed) (registered := fun g inside w member => ((index w).mpr ⟨g, inside, member⟩).1)
        nonempty found
    let cut := parkedProduceCommit (binds waiting) selected waiting (persistent waiting)
    refine ⟨cut, some work, by simp [cut, lockedProduce, lowerLocked, found, opens], admitted, ?_, ?_⟩
    · apply ParkedQuiet.shrink capture quiet
      · rw [waitCut]
        split
        · exact Finset.Subset.refl _
        · exact Finset.erase_subset _ _
      · rw [dataCut]
        simp [fire, lockedDataCommit]
    · constructor
      · intro impossible
        cases impossible
      · intro silent
        have notFound := (offer_search_none_iff_no_wake capture binds offer groups waiters
          (StoredValue live dataLabel) index distinct covered).mpr silent
        rw [found] at notFound
        cases notFound

/-- At a covered quiet cut a selected wake must use the actual
arrival. It cannot consume an unrelated join of old data and lose the
offered value. The incoming sentinel is not an installed occurrence. -/
theorem locked_wake_uses_offer {Wait : Type*} [DecidableEq Wait]
    (binds : Wait → List (Ch × Pat)) (offer : ProduceRequest Ch Val)
    (groups : List (WaitView Ch Val Wait)) (waiters : Finset Wait)
    (live : Finset (Ch × Int)) (label : Ch × Int → Val)
    (registered : ∀ group ∈ groups, ∀ waiter ∈ group.2, waiter ∈ waiters)
    (distinct : ∀ w ∈ waiters, ((binds w).map Prod.fst).Nodup)
    (covered : ∀ group ∈ groups, ∀ w ∈ group.2, ∀ slot ∈ binds w,
      ViewValues group.1 (StoredValue live label) slot.1)
    (quiet : ParkedQuiet capture binds waiters live label)
    {waiting : Wait} {selected : List (Match Val Arg)}
    (found : offerSearch capture binds offer groups = some (waiting, selected)) :
    ∃ row ∈ selected, row.datum = ⟨offer.2.1, -1, offer.2.2⟩ := by
  obtain ⟨_, group, _, layout, _, _, _, ordered, _, hit⟩ := (offer_search_winner_iff capture).mp found
  have inside : group ∈ groups := by rw [layout]; simp
  have visible : waiting ∈ group.2 := by apply List.mem_reverse.mp; rw [ordered]; simp
  have installed := registered group inside waiting visible
  have blocked := (packet_none_iff_not_readyOn capture (distinct waiting installed)
    (covered group inside waiting visible)).mpr (quiet waiting installed)
  exact arrival_used_of_blocked capture (distinct waiting installed) blocked hit

/-- Keep a persistent selected receiver and its index. Unlink a
linear selected receiver from its ordinary bucket. A produce miss
does not change the receiver index. -/
def JoinIndex.afterOffer {Wait : Type*} [DecidableEq Wait] (table : JoinIndex Ch Wait)
    (channels : Wait → List Ch) (persistent : Wait → Bool) : Option Wait → JoinIndex Ch Wait
  | none => table
  | some waiter => if persistent waiter then table else table.dropOrdinary (channels waiter) waiter

/-- Composition of the maintained lookup with the locked produce
cut. The next table agrees with the actual committed receiver set.
The order of bucket lookup and each shuffle still come from their
respective native inputs. -/
theorem indexed_produce_refines_cut {Wait Body Supply : Type*} [DecidableEq Wait]
    (randomOf : Val → Supply) (merge : Supply → Supply → List Supply → Supply)
    (binds : Wait → List (Ch × Pat)) (continuation : Wait → Body × Supply) (persistent peek : Wait → Bool)
    (offer : ProduceRequest Ch Val) (table : JoinIndex Ch Wait)
    (prepare : List Ch → ℕ → WaitView Ch Val Wait) (key : Int)
    (live : Finset (Ch × Int)) (waiters : Finset Wait) (dataLabel : Ch × Int → Val) (waitingLabel : Wait → Val)
    (roster : table.Covers (fun w => (binds w).map Prod.fst) waiters)
    (shuffles : ∀ entry ∈ (table.keysAt offer.1).zipIdx,
      (prepare entry.1 entry.2).2.Perm (table.waitersAt entry.1))
    (installedStay : ∀ ks w, w ∈ (table.installed ks).toList → persistent w = true)
    (distinct : ∀ w ∈ waiters, ((binds w).map Prod.fst).Nodup)
    (covered : ∀ group ∈ table.offerViews offer.1 prepare, ∀ w ∈ group.2, ∀ slot ∈ binds w,
      ViewValues group.1 (StoredValue live dataLabel) slot.1)
    (represented : ∀ group ∈ table.offerViews offer.1 prepare, ∀ source datum,
      datum ∈ group.1 source → (source, datum.index) ∈ live ∧ dataLabel (source, datum.index) = datum.raw)
    (indexed : ∀ group ∈ table.offerViews offer.1 prepare, ∀ source a b,
      a ∈ group.1 source → b ∈ group.1 source → a.index = b.index → a = b)
    (fresh : offerSearch capture binds offer (table.offerViews offer.1 prepare) = none →
      (offer.1, key) ∉ live ∧ dataLabel (offer.1, key) = offer.2.1)
    (quiet : ParkedQuiet capture binds waiters live dataLabel) :
    let groups := table.offerViews offer.1 prepare
    let next := table.afterOffer (fun w => (binds w).map Prod.fst) persistent
      ((offerSearch capture binds offer groups).map Prod.fst)
    ∃ cut work, lockedProduce capture randomOf merge binds continuation persistent peek offer groups key =
        some (cut, work) ∧
      Enabled (Sum.elim dataLabel waitingLabel) (live.disjSum waiters) cut ∧
      ParkedQuiet capture binds (fire (live.disjSum waiters) cut).toRight
        (fire (live.disjSum waiters) cut).toLeft dataLabel ∧
      (work = none ↔ ∀ w ∈ waiters, offer.1 ∈ (binds w).map Prod.fst →
        ¬ ReadyOn capture (offeredValues (StoredValue live dataLabel) offer) (binds w)) ∧
      next.Covers (fun w => (binds w).map Prod.fst) (fire (live.disjSum waiters) cut).toRight := by
  let groups := table.offerViews offer.1 prepare
  have exactIndex (w : Wait) := JoinIndex.offerViews_cover roster offer.1 prepare shuffles w
  obtain ⟨cut, work, run, admitted, stopped, exactMiss⟩ := locked_produce_refines_cut capture
    randomOf merge binds continuation persistent peek offer groups key live waiters dataLabel waitingLabel
    exactIndex distinct covered represented indexed fresh quiet
  refine ⟨cut, work, run, admitted, stopped, exactMiss, ?_⟩
  change (table.afterOffer (fun w => (binds w).map Prod.fst) persistent
    ((offerSearch capture binds offer groups).map Prod.fst)).Covers
      (fun w => (binds w).map Prod.fst) (fire (live.disjSum waiters) cut).toRight
  cases chosen : offerSearch capture binds offer groups with
  | none =>
    have allocation := run
    rw [lockedProduce, chosen, lowerLocked] at allocation
    have shape := (Prod.mk.inj (Option.some.inj allocation)).1
    rw [← shape]
    simpa [JoinIndex.afterOffer, fire] using roster
  | some hit =>
    obtain ⟨w, packet⟩ := hit
    have dispatches := run
    rw [lockedProduce, chosen, lowerLocked] at dispatches
    obtain ⟨job, prepared, same⟩ := Option.map_eq_some_iff.mp dispatches
    obtain ⟨batch, _, rfl⟩ := Option.map_eq_some_iff.mp prepared
    have shape := (Prod.mk.inj same).1
    rw [← shape, (parked_produce_projects (binds w) packet live waiters w (persistent w)).2]
    cases flag : persistent w with
    | true => simpa [JoinIndex.afterOffer, flag] using roster
    | false =>
      have ordinary : w ∉ (table.installed ((binds w).map Prod.fst)).toList := by
        intro installed
        have equal := installedStay _ _ installed
        rw [flag] at equal
        cases equal
      simpa [JoinIndex.afterOffer, flag] using JoinIndex.drop_covers roster w ordinary

end OfferHandoff

/-- Repost the raw, nonpersistent data, not the captures. This is a bag
observation of the publication packet, not its scheduling order. -/
def peekReposts {K : Type*} (binds : List (Ch × Pat)) (packet : List (Match Val Arg)) :
    Multiset (RhoLbl Ch Val Pat K) :=
  ((repostRequests binds packet).map fun (channel, value, _) => .msg channel value : List (RhoLbl Ch Val Pat K))

omit [DecidableEq Ch] in
theorem peekReposts_le_messages {K : Type*} :
    ∀ (binds : List (Ch × Pat)) (packet : List (Match Val Arg)),
      peekReposts (K := K) binds packet ≤ msgs .msg binds (packet.map fun row => row.datum.raw)
  | [], _ => by simp [peekReposts, repostRequests, msgs]
  | _ :: _, [] => by simp [peekReposts, repostRequests, msgs]
  | bind :: binds, row :: packet => by
      have smaller := peekReposts_le_messages (K := K) binds packet
      by_cases persistent : row.datum.persistent = true
      · simpa [peekReposts, repostRequests, msgs, persistent] using
          smaller.trans (Multiset.le_cons_self _ (.msg bind.1 row.datum.raw))
      · simpa [peekReposts, repostRequests, msgs, persistent] using
          (Multiset.cons_le_cons (.msg bind.1 row.datum.raw) smaller)

section Publication

variable {R : Type*} [DecidableEq R]

/-- The locked match detaches the linear data. Body and repost effects
belong to a later stage; publishing them here would hide the locked cut. -/
def detachPeek (rule : Rule R) (withheld : Multiset R) : Rule R :=
  ⟨rule.take + withheld, rule.keep - withheld, 0, rule.closed⟩

def publishRows (rows : Multiset R) : Rule R := ⟨0, 0, rows, fun _ => false⟩

theorem detachPeek_enabled_iff (rule : Rule R) (withheld world : Multiset R)
    (part : withheld ≤ rule.keep) : (detachPeek rule withheld).Enabled world ↔ rule.Enabled world := by
  have same : (detachPeek rule withheld).redex = rule.redex := by
    change rule.take + withheld + (rule.keep - withheld) = rule.take + rule.keep
    rw [add_assoc, add_tsub_cancel_of_le part]
  unfold Rule.Enabled
  rw [same]
  rfl

/-- A settled read observation is exact after both sets of outputs have
been published, without interfering reactions. In the interpreter, a
repost is itself a produce and need not be an isolated publication. -/
theorem isolated_peek_settles (rule : Rule R) (withheld world : Multiset R)
    (part : withheld ≤ rule.keep) (enabled : rule.Enabled world) :
    let cut := (detachPeek rule withheld).result world
    Reduces (· = detachPeek rule withheld) world cut ∧
    (Reduces (· = publishRows withheld) cut ((publishRows withheld).result cut) ∧
      Reduces (· = publishRows rule.make) ((publishRows withheld).result cut) (rule.result world)) ∧
    (Reduces (· = publishRows rule.make) cut ((publishRows rule.make).result cut) ∧
      Reduces (· = publishRows withheld) ((publishRows rule.make).result cut) (rule.result world)) := by
  have fits : withheld ≤ world - rule.take :=
    le_trans part (le_tsub_of_add_le_left enabled.1)
  have restored : world - (rule.take + withheld) + withheld = world - rule.take := by
    rw [← tsub_tsub, tsub_add_cancel_of_le fits]
  have canPublish (rows state : Multiset R) : (publishRows rows).Enabled state :=
    ⟨by simp [publishRows, Rule.redex], avoids_none _⟩
  refine ⟨⟨_, rfl, (detachPeek_enabled_iff _ _ _ part).mpr enabled, rfl⟩,
    ⟨⟨_, rfl, canPublish _ _, rfl⟩, ?_⟩, ⟨⟨_, rfl, canPublish _ _, rfl⟩, ?_⟩⟩
  · refine ⟨_, rfl, canPublish _ _, ?_⟩
    simp only [Rule.result, detachPeek, publishRows, tsub_zero, add_zero, restored]
  · refine ⟨_, rfl, canPublish _ _, ?_⟩
    simp only [Rule.result, detachPeek, publishRows, tsub_zero, add_zero]
    rw [add_right_comm, restored]

end Publication

end Prepared

end Rholang

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
