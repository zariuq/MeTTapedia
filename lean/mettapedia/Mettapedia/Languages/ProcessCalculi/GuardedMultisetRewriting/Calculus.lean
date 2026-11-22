import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Reflection
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.ValuesAndSpaces
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Matching
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedSharing

/-!
# Guarded multiset rewriting, assembled

Pattern variables are instantiated by one-sided matching. Shared live logic
variables and two-sided equation solving are outside this step definition.

**Terms.** Values of a term layer (`Sources.TermLayer`): terms, patterns with variables, and a
declared theory `E` saying which terms are equal. The reference instance is binding trees
(`SharedTerms.treeLayer`): nameless trees, so alpha-equivalent terms are equal, stored as shared
DAGs with shifts on edges, where equal terms are one reference (`SharedTerms.unfold_eq_iff`,
`SharedTerms.alphaEq_iff_same_ref`) and running on references is running on trees
(`sharedStep_sound`, `sharedStep_complete`).

**Configurations.** Bags of terms; each term lives in a space (`Calculus.space`). Spaces are
locations reached through handles that carry rights (`InteractionTypes.Rights`): `receive` to take,
`peek` to read, `send` to produce, `observe` to check what is there. A handle with fewer rights is
the same space with fewer rights.

**One rule, the step** (`Step`, the two-line law):

```
S ⊎ σT ⊎ σR  →  S ⊎ σR ⊎ σP
  if σ matches the take patterns to distinct terms σT and the read patterns to terms of σR
  (each read term counted once; read patterns may share one), and every check σC holds in the
  state before
whenever r: r stays parked (its term is read by each of its steps) and fires each time it is enabled
```

A process runs only rules formed under its rights (`Formed`), so a step is atomic and checked:
everything it takes, reads, makes and checks lies where the process holds the right
(`Process.Step.permitted`). For the compiled transforms this is the formation of the interaction
semantics (`formedUnder_of_fires`, into `InteractionTypes.FormedUnder`).

**Reflection.** Each rule selects its declared value or syntax reading
(`Contract`, `Readers`). These mathematical readings do not prescribe a
language's parameter-type spellings. A step only copies what it read into
its templates (`data_stays_data`); only `eval` runs stored code (`EvalStep`). Sealed spaces keep
their equations (`sealed_bisimulation`); unrestricted syntax readers collapse them (`data_reader_collapses`).

**Derived forms, and who owns them.**

* rho's COMM is a step taking two: `Equivalence.rholang_correspond` (every Rholang reduction rule is
  a rule the transform definitions generate) and `Equivalence.bisimilar_rholang_iff`.
* `match` is the read-only restriction: `Equivalence.Lanes.prime_match_specializes_every` (an
  `every` over a read takes nothing and makes the bag of instances).
* `=`-rules are a read-only rule space plus demand: `MeTTaZero.evaluationFiring` (work and answer
  routing), `MeTTaZero.loop_delivers_iff_runner_completes`, and the absence decision behind answers,
  `MeTTaZero.answer_not_stable_under_new_equation`; a rule kept parked is `Reflection.RulesAsData`.
* Need cells are shared nodes: keying each demand by its term's reference shares exactly the demands
  for alpha-equivalent terms (`nodeSharing_sound`, `nodeSharing_complete`, new here, over
  `ProofRelevantNeed.SharingScheme`).
* LCF: only the kernel's steps make theorems when only the kernel holds `send` at the theorem space
  (`Process.Step.no_make_without_send`, new here at the level of the step; the run-level forms are
  `RegionPermissions.board_verdicts_derivable` and the tier-0 kernel's rights theorem).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe uV uT uP uN

/-- **The guarded rewriting calculus**: terms read as values and as syntax, and the space of each term. -/
structure Calculus (V : Type uV) (T : Type uT) (P : Type uP) (N : Type uN) where
  /-- Terms read through the declared value equality. -/
  asValues : TermLayer V T P
  /-- Terms read through the declared syntax equality. -/
  asSyntax : TermLayer V T P
  /-- Syntax is finer than value equality. -/
  finer : ∀ a b, asSyntax.E a b → asValues.E a b
  /-- The space each term lives in. -/
  space : T → N

namespace Calculus

variable {V : Type uV} {T : Type uT} {P : Type uP} {N : Type uN} (C : Calculus V T P N)

/-- The two readings of the declaration contract. -/
def readers : Readers V T P := ⟨C.asValues, C.asSyntax, C.finer⟩

/-- **A rule formed under rights**: it takes only from spaces where it may `receive`, reads only
where it may `peek`, produces only where it may `send`, checks only where it may `observe`. -/
structure Formed (Γ : Rights N) (contract : Contract) (r : Rule V T P) : Prop where
  take : ∀ p ∈ r.take, ∀ (σ : Subst V T) (t : T), (C.readers.layer contract).Solves σ p t →
    Γ (C.space t) .receive = true
  read : ∀ p ∈ r.read, ∀ (σ : Subst V T) (t : T), (C.readers.layer contract).Solves σ p t →
    Γ (C.space t) .peek = true
  produce : ∀ p ∈ r.produce, ∀ (σ : Subst V T) (t : T), (C.readers.layer contract).inst σ p = some t →
    Γ (C.space t) .send = true
  check : ∀ c ∈ r.checks, ∀ (σ : Subst V T) (t : T),
    (C.readers.layer contract).Covers σ c.pattern t → Γ (C.space t) .observe = true

/-- **A process**: the rights its handles carry, and its rules, each with its contract and formed
under those rights. -/
structure Process where
  rights : Rights N
  rules : List (Contract × Rule V T P)
  formed : ∀ cr ∈ rules, C.Formed rights cr.1 cr.2

end Calculus

variable {V : Type uV} {T : Type uT} {P : Type uP} {N : Type uN} {C : Calculus V T P N}

/-- **The step of a process**: one of its rules steps by the two-line law, read through its
contract. -/
def Calculus.Process.Step (proc : C.Process) (M M' : Multiset T) : Prop :=
  ProgramStep C.readers proc.rules M M'

theorem mem_of_mapM {f : P → Option T} :
    ∀ {ps : List P} {ts : List T}, ps.mapM f = some ts → ∀ t ∈ ts, ∃ p ∈ ps, f p = some t
  | [], ts, h, t, m => by
      have h' : (some [] : Option (List T)) = some ts := h
      cases h'
      simp at m
  | p :: ps, ts, h, t, m => by
      rw [List.mapM_cons] at h
      cases hp : f p with
      | none => rw [hp] at h; cases h
      | some u =>
          cases hps : ps.mapM f with
          | none => rw [hp, hps] at h; cases h
          | some us =>
              rw [hp, hps] at h
              have h' : some (u :: us) = some ts := h
              cases h'
              rcases List.mem_cons.mp m with rfl | m
              · exact ⟨p, by simp, hp⟩
              · obtain ⟨q, qm, hq⟩ := mem_of_mapM hps t m
                exact ⟨q, by simp [qm], hq⟩

theorem mem_of_instTemplate {L : TermLayer V T P} {σ : Subst V T} {ps : List P} {ts : List T}
    (h : instTemplate L σ ps = some ts) : ∀ t ∈ ts, ∃ p ∈ ps, L.inst σ p = some t :=
  mem_of_mapM h

theorem mem_of_forall₂ {Q : P → T → Prop} :
    ∀ {ps : List P} {ts : List T}, List.Forall₂ Q ps ts → ∀ t ∈ ts, ∃ p ∈ ps, Q p t
  | [], [], .nil, _, m => by simp at m
  | p :: _, _ :: _, .cons h rest, t, m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact ⟨p, by simp, h⟩
      · obtain ⟨q, qm, hq⟩ := mem_of_forall₂ rest t m
        exact ⟨q, by simp [qm], hq⟩

/-- **A step is permitted by the process's rights**: it takes only where the process may
`receive`, reads only where it may `peek`, makes only where it may `send`, and everything a check
matches lies where it may `observe`. -/
theorem Calculus.Process.Step.permitted {proc : C.Process} {M M' : Multiset T}
    (step : proc.Step M M') :
    ∃ cr ∈ proc.rules, ∃ (σ : Subst V T) (S taken kept : Multiset T) (made : List T),
      M = S + taken + kept ∧ M' = S + kept + made ∧
      (∀ t ∈ taken, proc.rights (C.space t) .receive = true) ∧
      (∀ t ∈ kept, proc.rights (C.space t) .peek = true) ∧
      (∀ t ∈ made, proc.rights (C.space t) .send = true) ∧
      (∀ c ∈ cr.2.checks, ∀ t, (C.readers.layer cr.1).Covers σ c.pattern t →
        proc.rights (C.space t) .observe = true) := by
  obtain ⟨cr, mem, σ, S, _, kept, made, -, ⟨ts₁, sol₁, rfl⟩, ⟨ts₂, sol₂, keptLe, -⟩, hM, -, inst,
    hM'⟩ := step
  have formed := proc.formed cr mem
  refine ⟨cr, mem, σ, S, ts₁, kept, made, hM, hM', fun t m => ?_, fun t m => ?_, fun t m => ?_,
    fun c cm t cov => formed.check c cm σ t cov⟩
  · obtain ⟨p, pm, h⟩ := mem_of_forall₂ sol₁ t (by simpa using m)
    exact formed.take p pm σ t h
  · obtain ⟨p, pm, h⟩ := mem_of_forall₂ sol₂ t (by simpa using Multiset.mem_of_le keptLe m)
    exact formed.read p pm σ t h
  · obtain ⟨p, pm, h⟩ := mem_of_instTemplate inst t m
    exact formed.produce p pm σ t h

/-- **No `send`, no new terms**: a process that does not hold `send` at a space never adds a term
there. With the theorem space writable only by the kernel, only kernel steps make theorems. -/
theorem Calculus.Process.Step.no_make_without_send [DecidableEq N] {proc : C.Process}
    {M M' : Multiset T} (step : proc.Step M M') {n : N} (noSend : proc.rights n .send = false) :
    snapshot C.space n M' ≤ snapshot C.space n M := by
  obtain ⟨cr, mem, σ, S, taken, kept, made, hM, hM', -, -, sends, -⟩ := step.permitted
  have none : snapshot C.space n (made : Multiset T) = 0 :=
    Multiset.filter_eq_nil.mpr fun t m h => by
      have := sends t (by simpa using m)
      rw [h, noSend] at this; cases this
  rw [hM', hM]
  simp only [snapshot_add, none, add_zero]
  rw [add_right_comm]
  exact Multiset.le_add_right _ _

/-! ## Formation is the interaction semantics' formation -/

/-- **A formed rule's compiled transform fires only formed steps**: every `Commit` it fires is
`FormedUnder` the process's rights, in the sense of the interaction semantics. -/
theorem formedUnder_of_fires {O : Type*} [DecidableEq O] [DecidableEq V] {Γ : Rights N}
    {contract : Contract} {r : Rule V T P} (formed : C.Formed Γ contract r) {absent : List P}
    (checks : r.checks = absent.map Check.absent) {m : Matcher V T P}
    (sound : Matcher.Sound (C.readers.layer contract) m)
    (complete : Matcher.Complete (C.readers.layer contract) m)
    (minimal : Matcher.Minimal (C.readers.layer contract) m)
    {label : O → T} {S : Finset O} {c : Commit O T}
    (fires : Fires (C.readers.layer contract) m label S (r.transform absent) c) :
    FormedUnder label C.space Γ c := by
  obtain ⟨y, row, -, commit⟩ := declarative_of_fires sound complete minimal
    (fun eval mem => by rw [lets_transform] at mem; cases mem) fires
  obtain ⟨σ, os₁, os₂, made, -, -, solves₁, solves₂, -, inst, rfl⟩ :=
    (dRow_transform_iff r absent y).mp row
  rw [footprint_row] at commit
  refine ⟨fun o mem => ?_, fun o mem => ?_, fun o mem => ?_, fun q mem t hq => ?_⟩
  · rw [commit.taken] at mem
    have om : o ∈ os₁ := by simpa using mem
    obtain ⟨p, pm, h⟩ := mem_of_forall₂ solves₁ (label o) (List.mem_map_of_mem om)
    exact formed.take p pm σ _ h
  · rw [commit.kept] at mem
    have om : o ∈ os₂ := by simpa using mem
    obtain ⟨p, pm, h⟩ := mem_of_forall₂ solves₂ (label o) (List.mem_map_of_mem om)
    exact formed.read p pm σ _ h
  · have hm : labels label c.made = (made : Multiset T) := commit.made
    have inMade : label o ∈ (made : Multiset T) := by
      rw [← hm]
      exact Multiset.mem_map_of_mem label (Finset.mem_val.mpr mem)
    obtain ⟨p, pm, h⟩ := mem_of_instTemplate inst (label o) (by simpa using inMade)
    exact formed.produce p pm σ _ h
  · have qm := (commit.queries q).mp mem
    simp only [Multiset.mem_coe, List.mem_map] at qm
    obtain ⟨a, am, rfl⟩ := qm
    have cov : (C.readers.layer contract).Covers σ a t := (semRegion_eq_true _).mp hq
    exact formed.check (Check.absent a) (by rw [checks]; exact List.mem_map_of_mem am) σ t cov

/-! ## Need cells are shared nodes -/

section NeedSharing

open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open SharedTerms

variable {Head : Type} {Site : Type*}

/-- **Need cells keyed by shared nodes**: each demand site holds a reference to its term; demands
with the same reference share one cell. -/
def nodeSharing (term : Site → Ref) : SharingScheme Site := ⟨Ref, inferInstance, term⟩

/-- Sharing by node is sound: demands that share a cell demand the same term. -/
theorem nodeSharing_sound (St : Store Head) (term : Site → Ref) :
    (nodeSharing term).SoundFor (fun s => unfold St (term s)) := by
  intro left right shares
  change term left = term right at shares
  simp only [shares]

/-- **Sharing by node is complete**: in a canonical store, demands for equal (alpha-equivalent)
terms share one cell. -/
theorem nodeSharing_complete {St : Store Head} (canon : Canonical St) {term : Site → Ref}
    (canonical : ∀ s, CanonRef St (term s)) {left right : Site}
    (same : unfold St (term left) = unfold St (term right)) : (nodeSharing term).Shares left right :=
  (unfold_eq_iff canon (canonical left) (canonical right)).mp same

end NeedSharing

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
