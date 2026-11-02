import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection.QuotedNames
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceControls

/-!
# Reflection: data stays data, and restricted readers preserve value equality

**Data stays data.** A step makes only the instances of its rule's templates (`Step.made_are_instances`):
code held in a gathered value is copied into what the step makes, never run. Running stored code is
a step of its own, `eval`, whose products are the code's effects. For the compiled transforms the
same law is `Reflection.DataLaw.made_is_instance` and `no_hidden_write`, and `eval` is a firing
whose footprint is the code's effects (`DataLaw.evalTransform_row`).

**The declaration contract decides how a rule reads.** A rule selects one of
two term layers over the same values and patterns (`Readers`): `Lval`, whose
declared theory `E` says when two terms compute the same value, and `Lsyn`, which compares syntax.
These are mathematical reading profiles, independent of surface parameter-type names.

**The theorem.** A space `A` is **sealed from reflection** in a program when no rule read as syntax
can match a value of `A`. Then **replacing values of `A` by `E`-equal ones is invisible**: the
relation "equal outside `A`, `E`-equal inside `A`" is a bisimulation of the program's steps
(`sealed_bisimulation`). Equational reasoning about the values of `A` is sound.
This restriction on readers is distinct from locking definitions against revision.

**Wand's collapse, and why sealing avoids it.** If a syntax reader can read `A` with a ground
pattern for every value, then the only equivalence of values that no rule can break is syntactic
equality (`data_reader_collapses`, from `Reflection.collapse_to_E`): this is Wand's theorem that
unrestricted reflection makes the equational theory trivial. In a sealed space the respected
equivalence contains `E`, which is coarser than syntax as soon as the theory has one equation.

**Example** (`Example`): values are bags written `bag(x, y)`, and `bag` commutes in the value
theory. `bag(a, b)` and `bag(b, a)` compute the same bag. A value reader of the pattern
`bag(a, b)` steps on both; a syntax reader steps on `bag(a, b)` only (`syntax_reader_separates`,
`value_reader_same`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uV uT uP

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## Explicit `eval` -/

/-- **`eval`**: the step that takes a request to run stored code and produces the code's effects. It
is the one step whose products depend on what the code says. -/
def EvalStep (request : T → T) (effects : T → Multiset T) (M M' : Multiset T) : Prop :=
  ∃ (S : Multiset T) (code : T), M = S + {request code} ∧ M' = S + effects code

/-- **Data stays data**: an ordinary step adds the instances of its templates and nothing else; the
values it read contribute only through the pattern variables. -/
theorem data_stays_data [DecidableEq T] {L : TermLayer V T P} {r : Rule V T P} {M M' : Multiset T}
    (step : Step L r M M') :
    ∃ (σ : Subst V T) (made : List T), instTemplate L σ r.produce = some made ∧
      M' - (made : Multiset T) ≤ M := by
  obtain ⟨σ, S, kept, made, inst, hM', le⟩ := step.made_are_instances
  refine ⟨σ, made, inst, ?_⟩
  rw [hM', add_tsub_cancel_right]
  exact le

/-! ## Relations a rule cannot see -/

/-- A relation on values is **invisible** to a rule read through `L`: a pattern of the rule that
solves a value solves every related value, and each check holds alike at related states. -/
structure Invisible (L : TermLayer V T P) (r : Rule V T P) (Rel : T → T → Prop) : Prop where
  solves : ∀ p ∈ r.take ++ r.read, ∀ (σ : Subst V T) (a b : T), Rel a b → L.Solves σ p a →
    L.Solves σ p b
  checks : ∀ c ∈ r.checks, ∀ (σ : Subst V T) (M N : Multiset T), Multiset.Rel Rel M N →
    c.holds σ (matchesIn L σ c.pattern M) → c.holds σ (matchesIn L σ c.pattern N)

theorem exists_forall₂_of_rel {Rel : T → T → Prop} :
    ∀ (l : List T) (m : Multiset T), Multiset.Rel Rel (l : Multiset T) m →
      ∃ l' : List T, (l' : Multiset T) = m ∧ List.Forall₂ Rel l l'
  | [], m, h => by
      have h0 : Multiset.Rel Rel 0 m := by simpa using h
      have hm : m = 0 := Multiset.rel_zero_left.mp h0
      subst hm
      exact ⟨[], rfl, .nil⟩
  | a :: l, m, h => by
      rw [← Multiset.cons_coe, Multiset.rel_cons_left] at h
      obtain ⟨b, m', hab, rest, rfl⟩ := h
      obtain ⟨l', hl', fl⟩ := exists_forall₂_of_rel l m' rest
      exact ⟨b :: l', by rw [← Multiset.cons_coe, hl'], .cons hab fl⟩

theorem rel_coe_of_forall₂ {Rel : T → T → Prop} :
    ∀ {l l' : List T}, List.Forall₂ Rel l l' → Multiset.Rel Rel (l : Multiset T) (l' : Multiset T)
  | [], [], .nil => Multiset.Rel.zero
  | _ :: _, _ :: _, .cons h rest => by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe]
      exact Multiset.Rel.cons h (rel_coe_of_forall₂ rest)

theorem forall₂_carry {Q : P → T → Prop} {Rel : T → T → Prop} :
    ∀ {ps : List P} {ts ts' : List T}, (∀ p ∈ ps, ∀ a b, Rel a b → Q p a → Q p b) →
      List.Forall₂ Q ps ts → List.Forall₂ Rel ts ts' → List.Forall₂ Q ps ts'
  | [], [], [], _, .nil, .nil => .nil
  | p :: ps, a :: ts, b :: ts', carry, .cons hq rest, .cons hr rest' =>
      .cons (carry p (by simp) a b hr hq)
        (forall₂_carry (fun p' m => carry p' (by simp [m])) rest rest')

/-- **Reads carry across a relation the patterns cannot see.** If `σ` reads the patterns from
`kept`, and `kept` is related value by value to `kept'`, then `σ` reads them from `kept'`; a value
read by several patterns keeps one partner for all of them. -/
theorem reads_transfer {L : TermLayer V T P} {σ : Subst V T} {ps : List P} {Rel : T → T → Prop}
    (carry : ∀ p ∈ ps, ∀ a b, Rel a b → L.Solves σ p a → L.Solves σ p b)
    {kept kept' : Multiset T} (reads : Reads L σ ps kept) (rel : Multiset.Rel Rel kept kept') :
    Reads L σ ps kept' := by
  classical
  obtain ⟨ts, sol, le, support⟩ := reads
  obtain ⟨extra, hts⟩ := Multiset.le_iff_exists_add.mp le
  have inKept : ∀ a ∈ extra, a ∈ kept := fun a m =>
    support a (by rw [← Multiset.mem_coe, hts]; exact Multiset.mem_add.mpr (Or.inr m))
  let pick : T → T := fun a => if h : ∃ b ∈ kept', Rel a b then h.choose else a
  have pick_spec : ∀ a ∈ kept, pick a ∈ kept' ∧ Rel a (pick a) := by
    intro a m
    have h : ∃ b ∈ kept', Rel a b := Multiset.exists_mem_of_rel_of_mem rel m
    simp only [pick, dif_pos h]
    exact h.choose_spec
  have relExtra : Multiset.Rel Rel extra (extra.map pick) :=
    Multiset.rel_map_right.mpr
      (Multiset.rel_refl_of_refl_on fun a m => (pick_spec a (inKept a m)).2)
  have relAll : Multiset.Rel Rel (ts : Multiset T) (kept' + extra.map pick) := by
    rw [hts]; exact rel.add relExtra
  obtain ⟨ts', hts', f⟩ := exists_forall₂_of_rel ts _ relAll
  refine ⟨ts', forall₂_carry carry sol f, by rw [hts']; exact Multiset.le_add_right _ _, ?_⟩
  intro t' m
  rw [← Multiset.mem_coe, hts'] at m
  rcases Multiset.mem_add.mp m with m | m
  · exact m
  · obtain ⟨a, am, rfl⟩ := Multiset.mem_map.mp m
    exact (pick_spec a (inKept a am)).1

/-- **A step transfers along an invisible relation**: if the relation is reflexive and invisible
to the rule, a state related to one that steps also steps, to a related state. -/
theorem step_transfer {L : TermLayer V T P} {r : Rule V T P} {Rel : T → T → Prop}
    (refl : ∀ a, Rel a a) (invisible : Invisible L r Rel) {M N M' : Multiset T}
    (rel : Multiset.Rel Rel M N) (step : Step L r M M') :
    ∃ N', Step L r N N' ∧ Multiset.Rel Rel M' N' := by
  obtain ⟨σ, S, _, kept, made, only, ⟨ts₁, sol₁, rfl⟩, reads, hM, holds, inst, rfl⟩ := step
  have rel' := rel
  rw [hM] at rel'
  obtain ⟨N₀₁, N₂, rel₀₁, rel₂, rfl⟩ := Multiset.rel_add_left.mp rel'
  obtain ⟨S', N₁, relS, rel₁, rfl⟩ := Multiset.rel_add_left.mp rel₀₁
  obtain ⟨ts₁', h₁, f₁⟩ := exists_forall₂_of_rel ts₁ N₁ rel₁
  subst h₁
  refine ⟨S' + N₂ + made, ⟨σ, S', ts₁', N₂, made, only,
    ⟨ts₁', forall₂_carry (fun p m => invisible.solves p (by simp [m]) σ) sol₁ f₁, rfl⟩,
    reads_transfer (fun p m => invisible.solves p (by simp [m]) σ) reads rel₂,
    rfl, fun c mem => invisible.checks c mem σ _ _ rel (holds c mem), inst, rfl⟩, ?_⟩
  exact (relS.add rel₂).add (Multiset.rel_refl_of_refl_on fun x _ => refl x)

/-! ## Readers and programs -/

/-- How a rule reads what it gathers: as computed values (`Atom` parameters) or as syntax
(`(Data Atom)` parameters). -/
inductive Contract where
  | value
  | data
  deriving DecidableEq, Repr

/-- **Two readings of one set of values and patterns**: `Lval` compares computed values, `Lsyn`
compares syntax, and syntax is finer. -/
structure Readers (V : Type uV) (T : Type uT) (P : Type uP) where
  Lval : TermLayer V T P
  Lsyn : TermLayer V T P
  finer : ∀ a b, Lsyn.E a b → Lval.E a b

/-- The term layer of a contract. -/
def Readers.layer (R : Readers V T P) : Contract → TermLayer V T P
  | .value => R.Lval
  | .data => R.Lsyn

/-- **A program step**: one of the program's rules steps, read through its contract. -/
def ProgramStep (R : Readers V T P) (prog : List (Contract × Rule V T P)) (M M' : Multiset T) :
    Prop :=
  ∃ cr ∈ prog, Step (R.layer cr.1) cr.2 M M'

/-- A rule's checks see the `E`-related matches of two states alike. Absence and counts always do; a fold does when
it respects `E`. -/
def ChecksRespect (L : TermLayer V T P) (r : Rule V T P) : Prop :=
  ∀ c ∈ r.checks, ∀ (σ : Subst V T) (m n : Multiset T), Multiset.Rel L.E m n → c.holds σ m →
    c.holds σ n

/-- An absence check sees related matches alike, for any relation. -/
theorem absent_respects (Rel : T → T → Prop) (p : P) (σ : Subst V T) {m n : Multiset T}
    (rel : Multiset.Rel Rel m n) (holds : (Check.absent p : Check V T P).holds σ m) :
    (Check.absent p : Check V T P).holds σ n := by
  change n = 0
  change m = 0 at holds
  subst holds
  exact Multiset.rel_zero_left.mp rel

/-- A count check sees related matches alike, for any relation. -/
theorem count_respects (Rel : T → T → Prop) (p : P) (k : ℕ) (σ : Subst V T) {m n : Multiset T}
    (rel : Multiset.Rel Rel m n) (holds : (Check.count p k : Check V T P).holds σ m) :
    (Check.count p k : Check V T P).holds σ n := by
  change Multiset.card n = k
  change Multiset.card m = k at holds
  rw [← Multiset.card_eq_card_of_rel rel, holds]

/-- **A rule whose checks are absences and counts respects every theory.** -/
theorem checksRespect_of_counts (L : TermLayer V T P) (r : Rule V T P)
    (counts : ∀ c ∈ r.checks, (∃ p, c = Check.absent p) ∨ ∃ p k, c = Check.count p k) :
    ChecksRespect L r := by
  intro c mem σ m n rel holds
  rcases counts c mem with ⟨p, rfl⟩ | ⟨p, k, rfl⟩
  · exact absent_respects L.E p σ rel holds
  · exact count_respects L.E p k σ rel holds

/-- **A rule is sealed from `A`**: none of its patterns, gathers or checks, reaches a value of
`A`. -/
def SealedFrom (L : TermLayer V T P) (r : Rule V T P) (A : T → Prop) : Prop :=
  (∀ p ∈ r.take ++ r.read, ∀ (σ : Subst V T) (t : T), A t → ¬ L.Solves σ p t) ∧
    ∀ c ∈ r.checks, ∀ (σ : Subst V T) (t : T), A t → ¬ L.Covers σ c.pattern t

/-- **The space `A` is sealed from reflection** in the program: no rule read as syntax reaches it. -/
def SealedSpace (R : Readers V T P) (prog : List (Contract × Rule V T P)) (A : T → Prop) : Prop :=
  ∀ cr ∈ prog, cr.1 = .data → SealedFrom R.Lsyn cr.2 A

/-- **Equal outside `A`, equal computed values inside `A`.** -/
def SameOutside (R : Readers V T P) (A : T → Prop) (a b : T) : Prop :=
  a = b ∨ (A a ∧ A b ∧ R.Lval.E a b)

theorem sameOutside_refl (R : Readers V T P) (A : T → Prop) (a : T) : SameOutside R A a a :=
  Or.inl rfl

theorem sameOutside_symm (R : Readers V T P) (A : T → Prop) {a b : T}
    (h : SameOutside R A a b) : SameOutside R A b a := by
  rcases h with rfl | ⟨ha, hb, e⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hb, ha, R.Lval.equivalence.symm e⟩

theorem rel_filter {Rel : T → T → Prop} {p : T → Prop} [DecidablePred p]
    (resp : ∀ a b, Rel a b → (p a ↔ p b)) :
    ∀ {M N : Multiset T}, Multiset.Rel Rel M N → Multiset.Rel Rel (M.filter p) (N.filter p) := by
  intro M N rel
  induction rel with
  | zero => simp
  | @cons a b _ _ hab _ ih =>
      by_cases ha : p a
      · have hb : p b := (resp a b hab).mp ha
        rw [Multiset.filter_cons_of_pos _ ha, Multiset.filter_cons_of_pos _ hb]
        exact Multiset.Rel.cons hab ih
      · have hb : ¬ p b := fun hb => ha ((resp a b hab).mpr hb)
        rw [Multiset.filter_cons_of_neg _ ha, Multiset.filter_cons_of_neg _ hb]
        exact ih

/-- **A value rule cannot see `E`.** -/
theorem invisible_of_value {L : TermLayer V T P} {r : Rule V T P} {Rel : T → T → Prop}
    (sub : ∀ a b, Rel a b → L.E a b) (checks : ChecksRespect L r) : Invisible L r Rel where
  solves p _ σ a b hab solves := solves.of_equiv (sub a b hab)
  checks c mem σ M N rel holds := by
    refine checks c mem σ _ _ ?_ holds
    have filtered := rel_filter (p := fun t => semRegion L σ c.pattern t = true) (fun a b hab => by
      simp only [semRegion_eq_true]
      exact ⟨fun cov => cov.of_equiv (sub a b hab),
        fun cov => cov.of_equiv (L.equivalence.symm (sub a b hab))⟩) rel
    exact filtered.mono fun a _ b _ h => sub a b h

/-- **A sealed syntax rule cannot see what differs inside `A`.** -/
theorem invisible_of_sealed (R : Readers V T P) {r : Rule V T P} {A : T → Prop}
    (sealed : SealedFrom R.Lsyn r A) : Invisible R.Lsyn r (SameOutside R A) where
  solves p mem σ a b hab solves := by
    rcases hab with rfl | ⟨ha, _, _⟩
    · exact solves
    · exact absurd solves (sealed.1 p mem σ a ha)
  checks c mem σ M N rel holds := by
    have filtered := rel_filter (p := fun t => semRegion R.Lsyn σ c.pattern t = true)
      (fun a b hab => by
        rcases hab with rfl | ⟨ha, hb, _⟩
        · exact Iff.rfl
        · simp only [semRegion_eq_true]
          exact ⟨fun cov => absurd cov (sealed.2 c mem σ a ha),
            fun cov => absurd cov (sealed.2 c mem σ b hb)⟩) rel
    have same : matchesIn R.Lsyn σ c.pattern M = matchesIn R.Lsyn σ c.pattern N := by
      refine Multiset.rel_eq.mp (filtered.mono fun a am b _ hab => ?_)
      rcases hab with e | ⟨ha, _, _⟩
      · exact e
      · have cov := (Multiset.mem_filter.mp am).2
        rw [semRegion_eq_true] at cov
        exact absurd cov (sealed.2 c mem σ a ha)
    change c.holds σ (matchesIn R.Lsyn σ c.pattern M) at holds
    rw [← same]
    exact holds

/-- **Sealed spaces keep their equations.** If the space `A` is sealed from reflection and every
value rule's checks respect `E`, then replacing values of `A` by `E`-equal ones is invisible: the
relation "equal outside `A`, `E`-equal inside `A`" is a bisimulation of the program's steps. -/
theorem sealed_bisimulation (R : Readers V T P) {prog : List (Contract × Rule V T P)}
    {A : T → Prop} (sealed : SealedSpace R prog A)
    (checks : ∀ cr ∈ prog, cr.1 = .value → ChecksRespect R.Lval cr.2)
    {M N M' : Multiset T} (rel : Multiset.Rel (SameOutside R A) M N)
    (step : ProgramStep R prog M M') :
    ∃ N', ProgramStep R prog N N' ∧ Multiset.Rel (SameOutside R A) M' N' := by
  obtain ⟨⟨contract, r⟩, mem, step⟩ := step
  cases contract with
  | value =>
      have invisible := invisible_of_value (Rel := SameOutside R A)
        (fun a b h => by
          rcases h with rfl | ⟨_, _, e⟩
          · exact R.Lval.equivalence.refl a
          · exact e) (checks _ mem rfl)
      obtain ⟨N', stepN, relN⟩ := step_transfer (sameOutside_refl R A) invisible rel step
      exact ⟨N', ⟨_, mem, stepN⟩, relN⟩
  | data =>
      have invisible := invisible_of_sealed R (sealed _ mem rfl)
      obtain ⟨N', stepN, relN⟩ := step_transfer (sameOutside_refl R A) invisible rel step
      exact ⟨N', ⟨_, mem, stepN⟩, relN⟩

/-- The bisimulation in the other direction. -/
theorem sealed_bisimulation_symm (R : Readers V T P) {prog : List (Contract × Rule V T P)}
    {A : T → Prop} (sealed : SealedSpace R prog A)
    (checks : ∀ cr ∈ prog, cr.1 = .value → ChecksRespect R.Lval cr.2)
    {M N N' : Multiset T} (rel : Multiset.Rel (SameOutside R A) M N)
    (step : ProgramStep R prog N N') :
    ∃ M', ProgramStep R prog M M' ∧ Multiset.Rel (SameOutside R A) M' N' := by
  have rel' : Multiset.Rel (SameOutside R A) N M :=
    Multiset.rel_flip.mp (rel.mono fun a _ b _ h => sameOutside_symm R A h)
  obtain ⟨M', stepM, relM⟩ := sealed_bisimulation R sealed checks rel' step
  exact ⟨M', stepM, Multiset.rel_flip.mp (relM.mono fun a _ b _ h => sameOutside_symm R A h)⟩

/-! ## Wand's collapse for syntax readers -/

/-- The probe rule of a pattern: take one value matching it, produce nothing. -/
def probe (p : P) : Rule V T P := ⟨[p], [], [], []⟩

/-- A probe steps from a single value exactly when its pattern matches the value. -/
theorem probe_steps_iff [DecidableEq V] {L : TermLayer V T P} {p : P} {t : T} :
    (∃ M', Step L (probe p) {t} M') ↔ L.Covers (fun _ => none) p t := by
  constructor
  · rintro ⟨M', σ, S, _, kept, made, only, ⟨ts₁, sol₁, rfl⟩, ⟨ts₂, sol₂, -, -⟩, hM, -, -, -⟩
    cases sol₂
    match ts₁, sol₁, hM with
    | [u], .cons hu .nil, hM =>
        have hu' : u = t := by
          have mem : u ∈ ({t} : Multiset T) := by
            rw [hM]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr (by simp))))
          simpa using mem
        subst hu'
        refine ⟨σ, fun v a h => by simp at h, fun v notIn => only v (by simpa [probe] using notIn), hu⟩
  · rintro ⟨τ, step⟩
    refine ⟨0, τ, 0, {t}, 0, [], fun v notIn => ?_, ⟨[t], .cons step.solves .nil, by simp⟩,
      ⟨[], .nil, by simp, by simp⟩, by simp, fun c mem => by simp [probe] at mem, rfl, by simp⟩
    rw [step.only v (by simpa [probe] using notIn)]

/-- **Wand's collapse.** When syntax readers have a ground pattern for every value, two values that
no probe tells apart are equal in the readers' theory; for syntax readers that theory is syntax,
so an unrestricted reader leaves no equation but identity. -/
theorem data_reader_collapses [DecidableEq V] {L : TermLayer V T P}
    (ground : Reflection.HasGroundPatterns L) {t u : T}
    (indistinguishable : ∀ p : P, (∃ M', Step L (probe p) {t} M') ↔ (∃ M', Step L (probe p) {u} M')) :
    L.E t u := by
  obtain ⟨p, solves⟩ := ground t
  have stepT : ∃ M', Step L (probe p) {t} M' :=
    probe_steps_iff.mpr ⟨fun _ => none,
      ⟨Extends.refl _, fun _ _ => rfl, (solves _ t).mpr (L.equivalence.refl t)⟩⟩
  obtain ⟨τ, step⟩ := probe_steps_iff.mp ((indistinguishable p).mp stepT)
  exact (solves τ u).mp step.solves

/-! ## Example: bags as values, bags as syntax -/

namespace Example

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls

/-- `bag(a, b)`. -/
def bagAB : Tm Sig := bin .bag (k .a) (k .b)

/-- The two readers: `Lc` compares bags as values (`bag` commutes), `Ls` compares syntax. -/
def readers : Readers ℕ (Tm Sig) (Pat ℕ Sig) where
  Lval := Lc
  Lsyn := Ls
  finer a b h := by
    have : a = b := (syntactic_E_iff (V := ℕ)).mp h
    subst this
    exact Lc.equivalence.refl a

/-- `bag(a, b)` and `bag(b, a)` are one value and two pieces of syntax. -/
theorem one_value_two_syntaxes : Lc.E bagAB bagBA ∧ ¬ Ls.E bagAB bagBA := by
  refine ⟨(by decide : ceq bagComm bagAB bagBA = true), fun h => ?_⟩
  have := (syntactic_E_iff (V := ℕ)).mp h
  revert this
  decide

theorem covers_ground {L : TermLayer ℕ (Tm Sig) (Pat ℕ Sig)} {t : Tm Sig}
    (e : L.E bagAB t) (inst : ∀ σ, L.inst σ pBagAB = some bagAB) :
    L.Covers (fun _ => none) pBagAB t :=
  ⟨fun _ => none, ⟨Extends.refl _, fun _ _ => rfl, ⟨bagAB, inst _, e⟩⟩⟩

/-- **A value reader steps on both.** -/
theorem value_reader_same :
    (∃ M', Step Lc (probe pBagAB) {bagAB} M') ∧ (∃ M', Step Lc (probe pBagAB) {bagBA} M') :=
  ⟨probe_steps_iff.mpr (covers_ground (Lc.equivalence.refl _) fun _ => rfl),
    probe_steps_iff.mpr (covers_ground one_value_two_syntaxes.1 fun _ => rfl)⟩

/-- **A syntax reader steps on `bag(a, b)` only.** -/
theorem syntax_reader_separates :
    (∃ M', Step Ls (probe pBagAB) {bagAB} M') ∧ ¬ (∃ M', Step Ls (probe pBagAB) {bagBA} M') := by
  refine ⟨probe_steps_iff.mpr (covers_ground (Ls.equivalence.refl _) fun _ => rfl), fun h => ?_⟩
  obtain ⟨τ, step⟩ := probe_steps_iff.mp h
  obtain ⟨w, inst, e⟩ := step.solves
  have hw : w = bagAB := by
    have : Ls.inst τ pBagAB = some bagAB := rfl
    rw [this] at inst
    exact (Option.some.inj inst).symm
  subst hw
  exact one_value_two_syntaxes.2 e

end Example

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
