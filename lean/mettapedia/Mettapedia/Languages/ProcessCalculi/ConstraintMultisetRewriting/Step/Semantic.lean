import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceReadoutsTraces

/-!
# The ordinary step: queries that read labels through solutions

Ordinary query regions read labels through solutions: a region tests alike any terms that a solution
equates. Syntactic observation of labels belongs to declared reflection. The raw step
(`AnnotatedRuns.firstOrder`) keeps every region, so it is the reflection layer; the ordinary step
restricts it to the semantic firings.

## Semantic queries and firings

* A query **reads through solutions** (`ReadsThroughSolutions`) when, at every solution, its region
  gives one answer on terms the solution identifies. A **semantic query** (`SemanticQuery`) is a
  raw query with that proof. It is the same data as a region of the probes modulo the knowledge
  with a sighted set (`SemanticQuery.equivRegion`), and it observes as that probe
  (`SemanticQuery.observes_iff`).
* A firing is **semantic** (`IsSemantic`) when all its queries are. This is the hypothesis
  `Observation.QueriesReadThroughSolutions` of the congruence theorems (`isSemantic_iff`). A
  **semantic firing** (`SemanticFiring`) is a raw firing with that proof; one built from semantic
  queries is semantic by construction (`SemanticFiring.ofQueries`). Firings without queries are
  semantic (`isSemantic_of_queries_nil`), renaming keeps semantic firings semantic
  (`isSemantic_rename`), and over an action whose solutions identify only equal terms every firing
  is semantic (`isSemantic_of_faithful`).
* **Reading a test through the solution** (`throughSolutions`): a test of terms that respects the
  action's equivalence, applied to the term read at the solution, is a semantic region.

## The ordinary step and its transports

* **The ordinary step** (`semanticStep`) is the first-order step restricted to semantic firings
  (`Race.restrict`): admission, results and knowledge are those of the raw step
  (`semanticStep_admits_iff`).
* **Its transports**: configurations with the same solutions and occurrences
  (`semanticTransport`), and renamings of occurrences that keep labels (`semanticRenamingTransport`),
  restricted from the raw step's transports, since moving and residuating a firing keep it semantic.
* **Runs**: a raw run of semantic firings is a run of the ordinary step with the same end
  (`liftRun`, `liftRun_last`), and every run of the ordinary step is a raw run (`forgetRun`,
  `forgetRun_last`).

## Congruence of equivalence modulo the knowledge, discharged

The query hypothesis of `Observation.ModuloEquivalent.firing` and `.bisimulation` holds by
construction for the ordinary step.

* **Equivariance** (`ModuloEquivalent.semantic_firing`): a semantic firing and its renaming along
  the equivalence are admitted together, with equivalent results; the renamed firing is semantic.
* **Counterparts** (`ModuloEquivalent.semantic_counterpart`): with a fresh supply of the made
  labels, every admitted semantic firing has a renamed counterpart at the other state with an
  equivalent result.
* **Bisimulation** (`ModuloEquivalent.semantic_bisimilar`): with a fresh supply of every label
  (`FreshSupply`), equivalent configurations are bisimilar for the ordinary step labelled by rules
  (`ruleOffers`), and every run of the ordinary step has a counterpart run with an equivalent end
  (`ModuloEquivalent.semantic_run`).
* **Programs that name only escaped identities** (`ModuloEquivalent.program_bisimilar`): for a
  program whose offered firings are semantic and name only identities of `E`, configurations
  equivalent relative to `E` are bisimilar for the program, with no fresh supply: each offered
  firing is its own counterpart.

## Pointwise equivalence

Pointwise equivalence is not preserved by every admitted semantic firing: the obstruction
`Observation.NonPrincipalFirings.pointwise_not_congruence` uses a firing with no query
(`SemanticControls.pointwise_not_preserved`). It is preserved when the knowledge has a principal
answer (`PointwiseEquivalent.semantic_counterpart_of_principal`), hence for every admitted semantic
firing of the first-order profile (`firstOrder_pointwise_counterpart`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

open AnnotatedRuns
open Observation (QueriesReadThroughSolutions Region ModuloProbe Probe)

universe uT uS uO

/-! ## Semantic queries and firings -/

section Definitions

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- **A query reads labels through solutions**: at each solution, its region gives one answer on
terms that the solution identifies. -/
def ReadsThroughSolutions {O : Type uO} (query : PredicateQueryAdmission.Query T S O) : Prop :=
  ∀ σ {s t : T}, A.Solves σ (s, t) → query.region σ s = query.region σ t

/-- **A semantic query**: a raw query with a proof that its region reads labels through solutions. -/
abbrev SemanticQuery (O : Type uO) :=
  {query : PredicateQueryAdmission.Query T S O // ReadsThroughSolutions A query}

/-- **A semantic firing reads through solutions in every query.** -/
def IsSemantic {O : Type uO} (f : Firing T S O) : Prop :=
  ∀ query ∈ f.queries, ReadsThroughSolutions A query

/-- **A semantic firing**: a raw firing with a proof that its query regions read labels through
solutions. -/
abbrev SemanticFiring (O : Type uO) := {f : Firing T S O // IsSemantic A f}

variable {A}

/-- **A semantic query is a region of the probes modulo the knowledge with a sighted set.** -/
def SemanticQuery.equivRegion {O : Type uO} : SemanticQuery A O ≃ Region A × Finset O where
  toFun q := (⟨q.1.region, q.2⟩, q.1.seen)
  invFun p := ⟨⟨p.1.test, p.2⟩, p.1.respects⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A semantic query observes as the probe modulo the knowledge of its region.** -/
theorem SemanticQuery.observes_iff {O : Type uO} [DecidableEq O] (label : O → T) (q : SemanticQuery A O)
    (C : Configuration T O) :
    (Probe.ask q.1).Observes A label C ↔
      (ModuloProbe.ask (SemanticQuery.equivRegion q).1 q.1.seen).Observes label C :=
  Iff.rfl

/-- **Semantic firings are the firings of the congruence theorems' hypothesis.** -/
theorem isSemantic_iff {O : Type uO} [DecidableEq O] (f : Firing T S O) :
    IsSemantic A f ↔ QueriesReadThroughSolutions A f :=
  Iff.rfl

/-- **A firing built from semantic queries is semantic by construction.** -/
def SemanticFiring.ofQueries {O : Type uO} (rule : RuleInstance T) (queries : List (SemanticQuery A O))
    (selection : Selection O) : SemanticFiring A O :=
  ⟨⟨rule, queries.map Subtype.val, selection⟩, fun query member => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp member
    exact q.2⟩

/-- **A firing without queries is semantic.** -/
theorem isSemantic_of_queries_nil {O : Type uO} {f : Firing T S O} (none : f.queries = []) :
    IsSemantic A f := fun query member => by
  rw [none] at member
  cases member

/-- **Renaming keeps a firing semantic**: it changes only the sighted sets of its queries. -/
theorem isSemantic_rename {O : Type uO} (π : O ≃ O) {f : Firing T S O} (reads : IsSemantic A f) :
    IsSemantic A (f.rename π) := fun query member => by
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact reads original present

/-- Rename a semantic firing. -/
def SemanticFiring.rename {O : Type uO} (π : O ≃ O) (f : SemanticFiring A O) : SemanticFiring A O :=
  ⟨f.1.rename π, isSemantic_rename π f.2⟩

/-- **Over an action whose solutions identify only equal terms, every firing is semantic.** -/
theorem isSemantic_of_faithful {O : Type uO} (faithful : ∀ σ (s t : T), A.Solves σ (s, t) → s = t)
    (f : Firing T S O) : IsSemantic A f := by
  intro _ _ σ s t solved
  rw [faithful σ s t solved]

variable (A)

/-- **A test read through the solution**: a test of terms that respects the action's equivalence,
applied to the term read at the solution. -/
def throughSolutions {O : Type uO} (test : T → Bool) (respects : ∀ {s t : T}, A.E s t → test s = test t)
    (seen : Finset O) : SemanticQuery A O :=
  ⟨⟨fun σ t => test (A.apply σ t), seen⟩, by
    intro σ s t solved
    exact respects solved⟩

end Definitions

/-! ## The ordinary step -/

section Step

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The ordinary step**: the first-order step restricted to semantic firings. -/
abbrev semanticStep := Race.restrict (firstOrder A label).toStep (fun _ f => IsSemantic A f)

/-- Admission in the ordinary step is admission of the raw firing. -/
theorem semanticStep_admits_iff (C : Configuration T O) (f : SemanticFiring A O) :
    (semanticStep A label).Admits (s := C) f ↔ f.1.Valid A label C :=
  Iff.rfl

/-- The result in the ordinary step is the raw result. -/
theorem semanticStep_result (C : Configuration T O) (f : SemanticFiring A O)
    (admitted : (semanticStep A label).Admits (s := C) f) :
    (semanticStep A label).result f admitted = f.1.result label C :=
  rfl

/-- **Transport in the ordinary step**: configurations with the same solutions and occurrences. -/
def semanticTransport : Interface.Transport (semanticStep A label) :=
  Race.restrictTransport (firstOrderTransport A label) (fun _ f => IsSemantic A f)
    (fun _ _ reads => reads) (fun _ _ _ reads => reads)

/-- **Transport in the ordinary step renaming occurrences**: label-keeping renamings. -/
def semanticRenamingTransport : Interface.Transport (semanticStep A label) :=
  Race.restrictTransport (renamingTransport A label) (fun _ f => IsSemantic A f)
    (fun i _ reads => isSemantic_rename (RenamingIso.rename i) reads) (fun _ _ _ reads => reads)

variable {A label}

/-- **A raw run of semantic firings is a run of the ordinary step.** -/
def liftRun : {C : Configuration T O} → (r : (firstOrder A label).toStep.Run C) →
    (∀ x ∈ r.word, IsSemantic A x.2) → (semanticStep A label).Run C
  | _, .nil C, _ => .nil C
  | _, .cons f admitted rest, reads =>
      .cons ⟨f, reads _ List.mem_cons_self⟩ admitted
        (liftRun rest fun x member => reads x (List.mem_cons_of_mem _ member))

theorem liftRun_last : ∀ {C : Configuration T O} (r : (firstOrder A label).toStep.Run C)
    (reads : ∀ x ∈ r.word, IsSemantic A x.2), (liftRun r reads).last = r.last
  | _, .nil _, _ => rfl
  | _, .cons _ _ rest, reads =>
      liftRun_last rest fun x member => reads x (List.mem_cons_of_mem _ member)

/-- **Every run of the ordinary step is a raw run.** -/
def forgetRun : {C : Configuration T O} → (semanticStep A label).Run C → (firstOrder A label).toStep.Run C
  | _, .nil C => .nil C
  | _, .cons f admitted rest => .cons f.1 admitted (forgetRun rest)

theorem forgetRun_last : ∀ {C : Configuration T O} (r : (semanticStep A label).Run C),
    (forgetRun r).last = r.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => forgetRun_last rest

end Step

/-! ## Labels with fresh identities, and the ordinary step labelled by rules -/

section Supply

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- **A fresh supply**: every label that some identity carries is carried by identities outside every
finite set. -/
def FreshSupply (label : O → T) : Prop := ∀ o : O, ∀ G : Finset O, ∃ o', o' ∉ G ∧ label o' = label o

/-- **The ordinary step labelled by rules**: every semantic firing is offered under its rule. -/
def ruleOffers (A : SubstitutionAction T S) (r : RuleInstance T) (f : Firing T S O) : Prop :=
  f.rule = r ∧ IsSemantic A f

end Supply

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open Semantic

universe uT uS uO uL

/-! ## Equivalence modulo the knowledge is a congruence for the ordinary step -/

section Congruence

variable {T : Type uT} {S : Type uS} {O : Type uO} {A : SubstitutionAction T S} {label : O → T}
  {E : Finset O}

/-- **Equivariance modulo the knowledge for semantic firings**: at equivalent states, along a renaming
supported on the present occurrences, a semantic firing and its renaming are admitted together and
their results are equivalent, when the firing's made identities are absent from both states. -/
theorem ModuloEquivalent.semantic_firing [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) (f : SemanticFiring A O)
    (avoids : ∀ r ∈ f.1.selection.made, r ∉ C.present ∧ r ∉ D.present) :
    ∃ π : O ≃ O, RenamingUpTo (entailedSetoid A C.equations) label E π ∧
      (∀ r ∈ f.1.selection.made, π r = r) ∧
      ((SemanticFiring.rename π f).1.Valid A label D ↔ f.1.Valid A label C) ∧
      ModuloEquivalent A label E (f.1.result label C) ((SemanticFiring.rename π f).1.result label D) :=
  h.firing avoids f.2

/-- **Admitted semantic firings whose made identities avoid the other state keep the equivalence.** -/
theorem ModuloEquivalent.semantic_admitted [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) (f : SemanticFiring A O) (valid : f.1.Valid A label C)
    (avoids : ∀ r ∈ f.1.selection.made, r ∉ D.present) :
    ∃ π : O ≃ O, (SemanticFiring.rename π f).1.Valid A label D ∧
      ModuloEquivalent A label E (f.1.result label C) ((SemanticFiring.rename π f).1.result label D) :=
  h.admitted valid avoids f.2

/-- **Semantic firings that name only escaped identities keep the equivalence.** -/
theorem ModuloEquivalent.semantic_named_firing [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) (f : SemanticFiring A O) (named : f.1.names ⊆ E) :
    (f.1.Valid A label C ↔ f.1.Valid A label D) ∧
      ModuloEquivalent A label E (f.1.result label C) (f.1.result label D) :=
  h.named_firing named f.2

/-- **Counterparts of admitted semantic firings.** When the made labels have fresh identities outside
every finite set, every admitted semantic firing has a renamed counterpart at the other state, and
the results are equivalent. The renamed firing is semantic (`isSemantic_rename`). -/
theorem ModuloEquivalent.semantic_counterpart [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) {f : Firing T S O} (valid : f.Valid A label C)
    (reads : IsSemantic A f)
    (supply : ∀ r ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label r) :
    ∃ π : O ≃ O, (f.rename π).Valid A label D ∧
      ModuloEquivalent A label E (f.result label C) ((f.rename π).result label D) := by
  classical
  let M := f.selection.made.toFinset.filter (· ∈ D.present)
  let F := C.present ∪ D.present ∪ E ∪ f.names
  have inF_C : ∀ {o}, o ∈ C.present → o ∈ F := fun inC =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ inC))
  have inF_D : ∀ {o}, o ∈ D.present → o ∈ F := fun inD =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ inD))
  have inF_E : ∀ {o}, o ∈ E → o ∈ F := fun inE =>
    Finset.mem_union_left _ (Finset.mem_union_right _ inE)
  have madeNamed : ∀ {o}, o ∈ f.selection.made → o ∈ f.names := fun made => by
    simp [Firing.names, made]
  have madeOfM : ∀ {o}, o ∈ M → o ∈ f.selection.made := fun inM =>
    List.mem_toFinset.mp (Finset.mem_filter.mp inM).1
  have sub : M ⊆ F := fun o inM => inF_D (Finset.mem_filter.mp inM).2
  obtain ⟨ρ, keeps, moved, fixed⟩ := exists_fresh_relabelling M F sub
    fun m inM => supply m (madeOfM inM)
  have freshC : ∀ {r}, r ∈ f.selection.made → r ∉ C.present := fun made => made_fresh valid made
  have fixC : ∀ o ∈ C.present, ρ o = o := fun o inC =>
    fixed o (inF_C inC) fun inM => freshC (madeOfM inM) inC
  have fixE : ∀ o ∈ E, ρ o = o := fun o inE =>
    fixed o (inF_E inE) fun inM =>
      freshC (madeOfM inM) ((h.escaped_iff inE).mpr (Finset.mem_filter.mp inM).2)
  have stays : renameConfiguration ρ C = C := by
    show (⟨C.equations, C.present.map ρ.toEmbedding⟩ : Configuration T O) = C
    rw [finset_map_eq_self ρ fixC]
  have gValid : (f.rename ρ).Valid A label C := by
    have moved := (Firing.valid_rename A keeps f C).mpr valid
    rwa [stays] at moved
  have gResult : (f.rename ρ).result label C = renameConfiguration ρ (f.result label C) := by
    have moved := Firing.result_rename keeps f C
    rwa [stays] at moved
  have privateStep : PrivatelyEquivalent A label E (f.result label C) ((f.rename ρ).result label C) :=
    ⟨ρ, ⟨keeps, fixE⟩, by rw [gResult]; exact GuardFreeProcessOrders.SameUpTo.refl A _⟩
  have gAvoids : ∀ r ∈ (f.rename ρ).selection.made, r ∉ C.present ∧ r ∉ D.present := by
    intro r member
    change r ∈ f.selection.made.map ρ at member
    obtain ⟨r₀, made₀, rfl⟩ := List.mem_map.mp member
    by_cases inD : r₀ ∈ D.present
    · have out := moved r₀ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr made₀, inD⟩)
      exact ⟨fun inC => out (inF_C inC), fun inD' => out (inF_D inD')⟩
    · have same : ρ r₀ = r₀ := fixed r₀
        (Finset.mem_union_right _ (madeNamed made₀)) fun inM => inD (Finset.mem_filter.mp inM).2
      rw [same]
      exact ⟨freshC made₀, inD⟩
  obtain ⟨π, -, -, admits, results⟩ := h.firing gAvoids (isSemantic_rename ρ reads)
  refine ⟨ρ.trans π, ?_, ?_⟩
  · rw [Firing.rename_trans]
    exact admits.mpr gValid
  · rw [Firing.rename_trans]
    exact (PrivatelyEquivalent.modulo privateStep).trans results

/-- **Equivalence modulo the knowledge is a bisimulation of the ordinary step labelled by rules**,
given a fresh supply of every label. -/
theorem ModuloEquivalent.semantic_bisimilar [DecidableEq O] (supply : FreshSupply label)
    {C D : Configuration T O} (h : ModuloEquivalent A label E C D) :
    Race.Bisimilar A label (ruleOffers A) C D := by
  refine ⟨ModuloEquivalent A label E, ⟨?_, ?_, ?_⟩, h⟩
  · rintro X Y related r X' ⟨f, ⟨rfl, reads⟩, valid, rfl⟩
    obtain ⟨π, valid', results⟩ := related.semantic_counterpart valid reads fun o _ G => supply o G
    exact ⟨_, ⟨f.rename π, ⟨rfl, isSemantic_rename π reads⟩, valid', rfl⟩, results⟩
  · rintro X Y related r Y' ⟨g, ⟨rfl, reads⟩, valid, rfl⟩
    obtain ⟨π, valid', results⟩ := related.symm.semantic_counterpart valid reads fun o _ G => supply o G
    exact ⟨_, ⟨g.rename π, ⟨rfl, isSemantic_rename π reads⟩, valid', rfl⟩, results.symm⟩
  · intro _ _ _ atom
    exact atom.elim

/-- **Runs of the ordinary step have counterparts**: given a fresh supply of every label, every run
from one of two equivalent configurations is matched by a run from the other, with equivalent
ends. -/
theorem ModuloEquivalent.semantic_run [DecidableEq O] (supply : FreshSupply label) :
    ∀ {C : Configuration T O} (r : (semanticStep A label).Run C) {D : Configuration T O},
      ModuloEquivalent A label E C D →
        ∃ r' : (semanticStep A label).Run D, ModuloEquivalent A label E r.last r'.last
  | _, .nil _, D, h => ⟨.nil D, h⟩
  | _, .cons f admitted rest, _, h => by
      obtain ⟨π, valid', results⟩ := h.semantic_counterpart (f := f.1) admitted f.2 fun o _ G => supply o G
      obtain ⟨r', ends⟩ := ModuloEquivalent.semantic_run supply rest results
      exact ⟨.cons (SemanticFiring.rename π f) valid' r', ends⟩

/-- **A program whose offered firings are semantic and name only escaped identities**: configurations
equivalent modulo the knowledge relative to those identities are bisimilar for the program. Each
offered firing is its own counterpart, so no fresh supply is needed. -/
theorem ModuloEquivalent.program_bisimilar [DecidableEq O] {L : Type uL}
    {offers : L → Firing T S O → Prop}
    (named : ∀ ℓ f, offers ℓ f → f.names ⊆ E ∧ IsSemantic A f) {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) : Race.Bisimilar A label offers C D := by
  refine ⟨ModuloEquivalent A label E, ⟨?_, ?_, ?_⟩, h⟩
  · rintro X Y related ℓ X' ⟨f, offered, valid, rfl⟩
    obtain ⟨names, reads⟩ := named ℓ f offered
    obtain ⟨admits, results⟩ := related.named_firing names reads
    exact ⟨_, ⟨f, offered, admits.mp valid, rfl⟩, results⟩
  · rintro X Y related ℓ Y' ⟨g, offered, valid, rfl⟩
    obtain ⟨names, reads⟩ := named ℓ g offered
    obtain ⟨admits, results⟩ := related.named_firing names reads
    exact ⟨_, ⟨g, offered, admits.mpr valid, rfl⟩, results⟩
  · intro _ _ _ atom
    exact atom.elim

/-! ## Pointwise equivalence -/

/-- **With a principal answer, pointwise equivalence is kept by admitted semantic firings**: it is
then equivalence modulo the knowledge. -/
theorem PointwiseEquivalent.semantic_counterpart_of_principal [DecidableEq O] {C D : Configuration T O}
    {answer : S} (principal : A.Principal C.equations answer) (h : PointwiseEquivalent A label E C D)
    {f : Firing T S O} (valid : f.Valid A label C) (reads : IsSemantic A f)
    (supply : ∀ r ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label r) :
    ∃ π : O ≃ O, (f.rename π).Valid A label D ∧
      PointwiseEquivalent A label E (f.result label C) ((f.rename π).result label D) := by
  obtain ⟨π, admitted, results⟩ := (h.modulo_of_principal principal).semantic_counterpart valid reads supply
  exact ⟨π, admitted, results.pointwise⟩

end Congruence

section FirstOrderProfile

open Mettapedia.Logic.LP

variable {signature : LPSignature} [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] {O : Type uO} [DecidableEq O]
  {label : O → Term signature} {E : Finset O}

/-- **In the first-order profile, pointwise equivalence is kept by every admitted semantic firing**:
an admitted firing has consistent knowledge, which has a principal answer. -/
theorem firstOrder_pointwise_counterpart {C D : Configuration (Term signature) O}
    (h : PointwiseEquivalent (FirstOrder.action signature) label E C D)
    {f : Firing (Term signature) (Subst signature) O} (valid : f.Valid (FirstOrder.action signature) label C)
    (reads : IsSemantic (FirstOrder.action signature) f)
    (supply : ∀ r ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label r) :
    ∃ π : O ≃ O, (f.rename π).Valid (FirstOrder.action signature) label D ∧
      PointwiseEquivalent (FirstOrder.action signature) label E (f.result label C)
        ((f.rename π).result label D) := by
  have consistent : (FirstOrder.action signature).Consistent C.equations := by
    obtain ⟨σ, solved⟩ := valid.firing.consistent
    exact ⟨σ, problem_refines label f.selection f.rule σ solved⟩
  obtain ⟨π, admitted, results⟩ :=
    ((firstOrder_moduloEquivalent_iff_pointwise label E consistent).mpr h).semantic_counterpart
      valid reads supply
  exact ⟨π, admitted, results.pointwise⟩

end FirstOrderProfile

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

#print axioms SemanticQuery.equivRegion
#print axioms SemanticQuery.observes_iff
#print axioms isSemantic_iff
#print axioms SemanticFiring.ofQueries
#print axioms isSemantic_of_queries_nil
#print axioms isSemantic_rename
#print axioms isSemantic_of_faithful
#print axioms throughSolutions
#print axioms semanticStep_admits_iff
#print axioms semanticStep_result
#print axioms semanticTransport
#print axioms semanticRenamingTransport
#print axioms liftRun_last
#print axioms forgetRun_last
#print axioms Observation.ModuloEquivalent.semantic_firing
#print axioms Observation.ModuloEquivalent.semantic_admitted
#print axioms Observation.ModuloEquivalent.semantic_named_firing
#print axioms Observation.ModuloEquivalent.semantic_counterpart
#print axioms Observation.ModuloEquivalent.semantic_bisimilar
#print axioms Observation.ModuloEquivalent.semantic_run
#print axioms Observation.ModuloEquivalent.program_bisimilar
#print axioms Observation.PointwiseEquivalent.semantic_counterpart_of_principal
#print axioms Observation.firstOrder_pointwise_counterpart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic
