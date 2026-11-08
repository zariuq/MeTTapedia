import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Client-respecting observation: escape and private renaming

Fresh identities are interchangeable (`AnnotatedRuns.executable_rename`), but only while nobody
outside holds them. Forgetting every identity is an observation, not an equivalence that every
client respects: a client that already holds a reference to an occurrence tells apart a state where
that occurrence carries a label from one where a different occurrence carries it.

## Escape

A **client context** (`Client`) holds references (a list, so sharing is visible), the identities its
predicate queries sighted, the identities recorded as evidence and the identities named in published
rows. Its **escaped identities** (`Client.escaped`) are all of them. A run's predicate queries add
their sightings (`runSighted`, `Client.watch`).

## Private equivalence

A **private renaming** for a set `E` of escaped identities (`PrivateRenaming`) is a bijection of
identities that keeps labels and fixes every identity of `E`. Two configurations are **privately
equivalent** (`PrivatelyEquivalent`) when a private renaming carries the first to the second, up to
the solutions of its knowledge. It is an equivalence (`refl`, `symm`, `trans`), coarser for fewer
escaped identities (`mono`), and it descends to configuration classes (`ClassEquivalent`,
`privateEnd`).

* **Sharing and multiplicity are kept, not assumed**: a renaming is a bijection, so two positions of
  a list name one identity after renaming exactly when they did before (`sharing_rename`), and the bag
  of the labels present is kept (`PrivatelyEquivalent.labels_eq`).
* **Escaped identities are fixed**: an escaped identity is present at one state of an equivalent
  pair exactly when at the other (`PrivatelyEquivalent.escaped_iff`).

## Compatible with firings

* **Equivariance** (`PrivatelyEquivalent.firing`): along the renaming that relates two states, every
  firing at the first has its renamed counterpart at the second, admitted together
  (`Firing.valid_rename`), with results related by the same renaming (`Firing.result_rename`).
* **Firings and runs that name only escaped identities keep the equivalence**
  (`PrivatelyEquivalent.named_firing`, `named_run`, from `executable_rename` and `follow_rename`):
  such a firing is its own renaming (`Firing.rename_eq_self`).

## Clients respect it

A **probe** (`Probe`) observes a state through a held reference (is it present?), a predicate query
(the existing `PredicateQueryAdmission.Query.Ask`), or a guard (`Check`: an equation, an absence or a count,
asked at every solution). Its names are the reference or the identities the query claims to have seen.

* **Equivariance of probes** (`Probe.observes_rename`), from `holds_rename` and `queryHolds_rename`.
* **Clients respect private equivalence** (`PrivatelyEquivalent.observes`, `Client.respects`): a probe
  that names only escaped identities observes the same at equivalent states.
* **Answers** (`PrivatelyEquivalent.answer`): the identities a query's region holds at equivalent
  states agree on every escaped identity and in number; the private ones are renamed.

## Joint ends

A history also leaves a client context: what it sighted, recorded or published. A **joint end** is a
state with its client context, and two joint ends are equivalent when one private renaming relates
both parts (`JointEquivalent`). For a common client whose names are all fixed, this is private
equivalence (`jointEquivalent_iff`).

## Alternatives under fresh names

Renaming a firing's fresh output `r` to another fresh identity `r'` of the same label gives an
alternative admitted at the same state (`fresh_alternative_valid`). Its result is privately
equivalent to the original's for every client that has seen neither name
(`fresh_alternative_equivalent`), and a client holding `r` separates them
(`fresh_alternative_separated`).

## Controls (`ObservationControls`)

* Two states whose single rows `20` and `21` carry one label are privately equivalent when neither
  escaped (`private_rows`); a client holding `20` separates them (`held_reference_separates`), although
  their knowledge and their bags of labels, everything the forget-all end keeps, agree
  (`forget_all_not_respected`).
* A renaming that swaps an escaped identity with a private one is not private
  (`swap_escaped_not_private`), and the states it relates are separated (`escaped_swap_separated`).
* One occurrence referenced twice is not two occurrences: no renaming turns `[20, 20]` into `[20, 21]`
  (`shared_not_copied`), and a state with one row is not equivalent to a state with two
  (`copied_not_equivalent`).
* A record that escaped into evidence and was then consumed still separates the joint ends, although
  the states are equal (`evidence_outlives_record`).
* A record of a fresh name alone is relative to what was public before: two histories that each
  recorded their own fresh row and consumed it have equivalent joint ends when neither row was
  public, and are told apart once one was (`fresh_records_relative`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (regionOf fire)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Lists and finite sets fixed by a renaming -/

theorem list_map_eq_self {α : Type*} {g : α → α} : ∀ {l : List α}, (∀ a ∈ l, g a = a) → l.map g = l
  | [], _ => rfl
  | a :: rest, fixes => by
      rw [List.map_cons, fixes a List.mem_cons_self,
        list_map_eq_self fun x member => fixes x (List.mem_cons_of_mem _ member)]

omit [DecidableEq O] in
theorem finset_map_eq_self (π : O ≃ O) {s : Finset O} (fixes : ∀ o ∈ s, π o = o) :
    s.map π.toEmbedding = s := by
  ext o
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, member, rfl⟩
    rwa [fixes a member]
  · intro member
    exact ⟨o, member, fixes o member⟩

/-! ## Escape -/

/-- The identities a list of predicate queries sighted. -/
def sighted : List (PredicateQueryAdmission.Query T S O) → Finset O
  | [] => ∅
  | query :: rest => query.seen ∪ sighted rest

theorem mem_sighted {o : O} :
    ∀ {queries : List (PredicateQueryAdmission.Query T S O)},
      o ∈ sighted queries ↔ ∃ query ∈ queries, o ∈ query.seen
  | [] => by simp [sighted]
  | query :: rest => by
      rw [sighted, Finset.mem_union, mem_sighted]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- The identities the predicate queries of a run sighted. -/
def runSighted : List (Firing T S O) → Finset O
  | [] => ∅
  | f :: rest => sighted f.queries ∪ runSighted rest

theorem mem_runSighted {o : O} :
    ∀ {w : List (Firing T S O)}, o ∈ runSighted w ↔ ∃ f ∈ w, ∃ query ∈ f.queries, o ∈ query.seen
  | [] => by simp [runSighted]
  | f :: rest => by
      rw [runSighted, Finset.mem_union, mem_sighted, mem_runSighted]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- **A client context**: the references it holds, in order and with repetitions, so sharing is
visible; the identities its predicate queries sighted; the identities recorded as evidence; and the
identities named in published rows. -/
structure Client (O : Type uO) where
  held : List O
  sighted : Finset O
  evidence : Finset O
  published : Finset O

namespace Client

/-- **The escaped identities of a client context.** -/
def escaped (c : Client O) : Finset O :=
  c.held.toFinset ∪ c.sighted ∪ c.evidence ∪ c.published

theorem held_escaped (c : Client O) {o : O} (member : o ∈ c.held) : o ∈ c.escaped := by
  simp [escaped, member]

theorem sighted_escaped (c : Client O) : c.sighted ⊆ c.escaped := by
  intro o member
  simp [escaped, member]

theorem evidence_escaped (c : Client O) : c.evidence ⊆ c.escaped := by
  intro o member
  simp [escaped, member]

theorem published_escaped (c : Client O) : c.published ⊆ c.escaped := by
  intro o member
  simp [escaped, member]

/-- The client after watching a run: the run's sightings join its own. -/
def watch (c : Client O) (w : List (Firing T S O)) : Client O :=
  { c with sighted := c.sighted ∪ runSighted w }

/-- **Every identity a watched run's predicate queries sighted has escaped.** -/
theorem watch_escaped (c : Client O) {w : List (Firing T S O)} {f : Firing T S O} (inRun : f ∈ w)
    {query : PredicateQueryAdmission.Query T S O} (asked : query ∈ f.queries) :
    query.seen ⊆ (c.watch w).escaped := by
  intro o member
  have inRun : o ∈ runSighted w := mem_runSighted.mpr ⟨f, inRun, query, asked, member⟩
  simp [escaped, watch, inRun]

/-- Rename every identity a client context holds. -/
def rename (π : O ≃ O) (c : Client O) : Client O :=
  ⟨c.held.map π, c.sighted.map π.toEmbedding, c.evidence.map π.toEmbedding,
    c.published.map π.toEmbedding⟩

omit [DecidableEq O] in
theorem rename_refl (c : Client O) : c.rename (Equiv.refl O) = c := by
  obtain ⟨held, sighted, evidence, published⟩ := c
  simp [rename]

omit [DecidableEq O] in
theorem rename_trans (π ρ : O ≃ O) (c : Client O) : c.rename (π.trans ρ) = (c.rename π).rename ρ := by
  obtain ⟨held, sighted, evidence, published⟩ := c
  simp [rename, List.map_map, Finset.map_map, Equiv.trans_toEmbedding]

/-- A renaming that fixes every escaped identity fixes the client context. -/
theorem rename_eq_self (c : Client O) {π : O ≃ O} (fixes : ∀ o ∈ c.escaped, π o = o) :
    c.rename π = c := by
  obtain ⟨held, sighted, evidence, published⟩ := c
  simp only [escaped, Finset.mem_union, List.mem_toFinset] at fixes
  simp only [rename, Client.mk.injEq]
  exact ⟨list_map_eq_self fun o member => fixes o (Or.inl (Or.inl (Or.inl member))),
    finset_map_eq_self π fun o member => fixes o (Or.inl (Or.inl (Or.inr member))),
    finset_map_eq_self π fun o member => fixes o (Or.inl (Or.inr member)),
    finset_map_eq_self π fun o member => fixes o (Or.inr member)⟩

end Client

/-! ## Private renamings -/

/-- **A private renaming** for the escaped identities `E`: a bijection of occurrence identities that
keeps every label and fixes every escaped identity. -/
structure PrivateRenaming (label : O → T) (E : Finset O) (π : O ≃ O) : Prop where
  keeps : ∀ o, label (π o) = label o
  fixes : ∀ o ∈ E, π o = o

namespace PrivateRenaming

omit [DecidableEq O]

variable {label : O → T} {E E' : Finset O} {π ρ : O ≃ O}

theorem refl : PrivateRenaming label E (Equiv.refl O) := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem symm (h : PrivateRenaming label E π) : PrivateRenaming label E π.symm := by
  refine ⟨fun o => ?_, fun o member => ?_⟩
  · have kept := h.keeps (π.symm o)
    rw [Equiv.apply_symm_apply] at kept
    exact kept.symm
  · rw [Equiv.symm_apply_eq]
    exact (h.fixes o member).symm

theorem trans (h : PrivateRenaming label E π) (k : PrivateRenaming label E ρ) :
    PrivateRenaming label E (π.trans ρ) := by
  refine ⟨fun o => ?_, fun o member => ?_⟩
  · rw [Equiv.trans_apply, k.keeps, h.keeps]
  · rw [Equiv.trans_apply, h.fixes o member, k.fixes o member]

theorem mono (h : PrivateRenaming label E π) (fewer : E' ⊆ E) : PrivateRenaming label E' π :=
  ⟨h.keeps, fun o member => h.fixes o (fewer member)⟩

/-- An escaped identity is in a renamed set exactly when it is in the set. -/
theorem mem_map_iff (h : PrivateRenaming label E π) {o : O} (escaped : o ∈ E) (P : Finset O) :
    o ∈ P.map π.toEmbedding ↔ o ∈ P := by
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, member, moved⟩
    have same : a = o := π.injective (moved.trans (h.fixes o escaped).symm)
    rwa [← same]
  · intro member
    exact ⟨o, member, h.fixes o escaped⟩

end PrivateRenaming

/-! ## Renaming configurations -/

omit [DecidableEq O] in
theorem renameConfiguration_refl (C : Configuration T O) :
    renameConfiguration (Equiv.refl O) C = C := by
  obtain ⟨equations, present⟩ := C
  simp [renameConfiguration]

omit [DecidableEq O] in
theorem renameConfiguration_trans (π ρ : O ≃ O) (C : Configuration T O) :
    renameConfiguration (π.trans ρ) C = renameConfiguration ρ (renameConfiguration π C) := by
  obtain ⟨equations, present⟩ := C
  simp [renameConfiguration, Finset.map_map, Equiv.trans_toEmbedding]

omit [DecidableEq O] in
theorem sameUpTo_rename (A : SubstitutionAction T S) (π : O ≃ O) {C D : Configuration T O}
    (same : SameUpTo A C D) : SameUpTo A (renameConfiguration π C) (renameConfiguration π D) :=
  ⟨same.1, congrArg (fun present : Finset O => present.map π.toEmbedding) same.2⟩

omit [DecidableEq O] in
/-- **Renaming keeps the bag of labels present.** -/
theorem labels_rename {label : O → T} {π : O ≃ O} (keeps : ∀ o, label (π o) = label o)
    (present : Finset O) : (present.map π.toEmbedding).val.map label = present.val.map label := by
  rw [Finset.map_val, Multiset.map_map]
  have same : label ∘ π.toEmbedding = label := funext keeps
  rw [same]

omit [DecidableEq O] in
/-- **Renaming keeps sharing**: two positions of a list name one identity after renaming exactly when
they did before. -/
theorem sharing_rename (π : O ≃ O) (l : List O) (i j : ℕ) :
    (l.map π)[i]? = (l.map π)[j]? ↔ l[i]? = l[j]? := by
  simp only [List.getElem?_map]
  exact (Option.map_injective π.injective).eq_iff

/-! ## Private equivalence -/

section Equivalence

variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O)

/-- **Private equivalence relative to the escaped identities `E`**: a private renaming carries the
first configuration to the second, up to the solutions of its knowledge. -/
def PrivatelyEquivalent (C D : Configuration T O) : Prop :=
  ∃ π : O ≃ O, PrivateRenaming label E π ∧ SameUpTo A (renameConfiguration π C) D

namespace PrivatelyEquivalent

variable {A label E}

omit [DecidableEq O] in
theorem refl (C : Configuration T O) : PrivatelyEquivalent A label E C C :=
  ⟨Equiv.refl O, .refl, by rw [renameConfiguration_refl]; exact SameUpTo.refl A C⟩

omit [DecidableEq O] in
theorem symm {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D) :
    PrivatelyEquivalent A label E D C := by
  obtain ⟨π, priv, same⟩ := h
  refine ⟨π.symm, priv.symm, ?_⟩
  have back := sameUpTo_rename A π.symm same
  rw [← renameConfiguration_trans, Equiv.self_trans_symm, renameConfiguration_refl] at back
  exact sameUpTo_symm A back

omit [DecidableEq O] in
theorem trans {C D F : Configuration T O} (h : PrivatelyEquivalent A label E C D)
    (k : PrivatelyEquivalent A label E D F) : PrivatelyEquivalent A label E C F := by
  obtain ⟨π, priv, same⟩ := h
  obtain ⟨ρ, priv', same'⟩ := k
  refine ⟨π.trans ρ, priv.trans priv', ?_⟩
  rw [renameConfiguration_trans]
  exact GuardFreeProcessOrders.SameUpTo.trans A (sameUpTo_rename A ρ same) same'

omit [DecidableEq O] in
theorem of_sameUpTo {C D : Configuration T O} (same : SameUpTo A C D) :
    PrivatelyEquivalent A label E C D :=
  ⟨Equiv.refl O, .refl, by rw [renameConfiguration_refl]; exact same⟩

omit [DecidableEq O] in
/-- **Fewer escaped identities, a coarser equivalence.** -/
theorem mono {E' : Finset O} {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D)
    (fewer : E' ⊆ E) : PrivatelyEquivalent A label E' C D := by
  obtain ⟨π, priv, same⟩ := h
  exact ⟨π, priv.mono fewer, same⟩

omit [DecidableEq O] in
/-- Equivalent states have knowledge with the same solutions. -/
theorem solutions {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D) :
    A.Equivalent C.equations D.equations := by
  obtain ⟨π, -, same⟩ := h
  exact same.1

omit [DecidableEq O] in
/-- **Multiplicity is kept**: equivalent states have the same bag of labels present. -/
theorem labels_eq {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D) :
    C.present.val.map label = D.present.val.map label := by
  obtain ⟨π, priv, same⟩ := h
  rw [← labels_rename priv.keeps C.present]
  exact congrArg (fun present : Finset O => present.val.map label) same.2

omit [DecidableEq O] in
theorem card_eq {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D) :
    C.present.card = D.present.card := by
  have bags := congrArg Multiset.card h.labels_eq
  simpa only [Multiset.card_map, Finset.card_val] using bags

omit [DecidableEq O] in
/-- **Escaped identities are fixed**: present at one state of an equivalent pair exactly when at the
other. -/
theorem escaped_iff {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D) {o : O}
    (escaped : o ∈ E) : o ∈ C.present ↔ o ∈ D.present := by
  obtain ⟨π, priv, same⟩ := h
  rw [← same.2]
  exact (priv.mem_map_iff escaped C.present).symm

end PrivatelyEquivalent

/-- Private equivalence as a setoid on configurations. -/
def privateSetoid : Setoid (Configuration T O) where
  r := PrivatelyEquivalent A label E
  iseqv := ⟨PrivatelyEquivalent.refl, PrivatelyEquivalent.symm, PrivatelyEquivalent.trans⟩

/-- **Private equivalence of configuration classes.** -/
def ClassEquivalent : ConfigurationClass A O → ConfigurationClass A O → Prop :=
  Quotient.lift₂ (PrivatelyEquivalent A label E) fun _ _ _ _ first second =>
    propext ⟨fun h => ((PrivatelyEquivalent.of_sameUpTo (sameUpTo_symm A first)).trans h).trans
        (PrivatelyEquivalent.of_sameUpTo second),
      fun h => ((PrivatelyEquivalent.of_sameUpTo first).trans h).trans
        (PrivatelyEquivalent.of_sameUpTo (sameUpTo_symm A second))⟩

omit [DecidableEq O] in
theorem classEquivalent_mk (C D : Configuration T O) :
    ClassEquivalent A label E (ConfigurationClass.mk A C) (ConfigurationClass.mk A D) ↔
      PrivatelyEquivalent A label E C D :=
  Iff.rfl

/-- Private equivalence as a setoid on configuration classes. -/
def classSetoid : Setoid (ConfigurationClass A O) where
  r := ClassEquivalent A label E
  iseqv := ⟨fun x => Quotient.inductionOn x PrivatelyEquivalent.refl,
    fun {x y} => Quotient.inductionOn₂ x y fun _ _ h => PrivatelyEquivalent.symm h,
    fun {x y z} => Quotient.inductionOn₃ x y z fun _ _ _ h k => PrivatelyEquivalent.trans h k⟩

/-- **The client-respecting end of a configuration class**: its class up to private renaming. -/
def privateEnd (x : ConfigurationClass A O) : Quotient (classSetoid A label E) :=
  Quotient.mk (classSetoid A label E) x

omit [DecidableEq O] in
theorem privateEnd_eq_iff (x y : ConfigurationClass A O) :
    privateEnd A label E x = privateEnd A label E y ↔ ClassEquivalent A label E x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := classSetoid A label E) h⟩

end Equivalence

/-! ## Compatible with firings -/

section Firings

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

/-- **The identities a firing names**: those it takes, reads and makes, and those its predicate
queries sighted. -/
def _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.Firing.names
    (f : Firing T S O) : Finset O :=
  f.selection.taken.toFinset ∪ f.selection.read.toFinset ∪ f.selection.made.toFinset ∪
    sighted f.queries

/-- **A firing that names only fixed identities is its own renaming.** -/
theorem _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns.Firing.rename_eq_self
    (f : Firing T S O) {π : O ≃ O} (fixes : ∀ o ∈ f.names, π o = o) :
    f.rename π = f := by
  obtain ⟨rule, queries, ⟨taken, read, made⟩⟩ := f
  simp only [Firing.names, Finset.mem_union, List.mem_toFinset] at fixes
  have queriesFixed : queries.map (renameQuery π) = queries := by
    refine list_map_eq_self fun query member => ?_
    show (⟨query.region, query.seen.map π.toEmbedding⟩ : PredicateQueryAdmission.Query T S O) = query
    rw [finset_map_eq_self π fun o seen =>
      fixes o (Or.inr (mem_sighted.mpr ⟨query, member, seen⟩))]
  show (⟨rule, queries.map (renameQuery π), ⟨taken.map π, read.map π, made.map π⟩⟩ :
    Firing T S O) = ⟨rule, queries, ⟨taken, read, made⟩⟩
  rw [queriesFixed,
    list_map_eq_self (g := ⇑π) (l := taken) fun o member => fixes o (Or.inl (Or.inl (Or.inl member))),
    list_map_eq_self (g := ⇑π) (l := read) fun o member => fixes o (Or.inl (Or.inl (Or.inr member))),
    list_map_eq_self (g := ⇑π) (l := made) fun o member => fixes o (Or.inl (Or.inr member))]

/-- Admission along a renaming that relates two states. -/
theorem valid_renamed {π : O ≃ O} (keeps : ∀ o, label (π o) = label o) {C D : Configuration T O}
    (same : SameUpTo A (renameConfiguration π C) D) (f : Firing T S O) :
    (f.rename π).Valid A label D ↔ f.Valid A label C :=
  (Firing.valid_congr A label same).symm.trans (Firing.valid_rename A keeps f C)

/-- Results along a renaming that relates two states. -/
theorem result_renamed {π : O ≃ O} (keeps : ∀ o, label (π o) = label o) {C D : Configuration T O}
    (same : SameUpTo A (renameConfiguration π C) D) (f : Firing T S O) :
    SameUpTo A (renameConfiguration π (f.result label C)) ((f.rename π).result label D) := by
  rw [← Firing.result_rename keeps]
  exact (f.rename π).result_congr A label same

namespace PrivatelyEquivalent

/-- **Equivariance**: at a privately equivalent state, every firing has its renamed counterpart,
admitted together with it, and their results are privately equivalent again. -/
theorem firing {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D) (f : Firing T S O) :
    ∃ π : O ≃ O, PrivateRenaming label E π ∧ ((f.rename π).Valid A label D ↔ f.Valid A label C) ∧
      PrivatelyEquivalent A label E (f.result label C) ((f.rename π).result label D) := by
  obtain ⟨π, priv, same⟩ := h
  exact ⟨π, priv, valid_renamed priv.keeps same f, π, priv, result_renamed priv.keeps same f⟩

/-- **Firings that name only escaped identities keep the equivalence.** -/
theorem named_firing {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D)
    {f : Firing T S O} (named : f.names ⊆ E) :
    (f.Valid A label C ↔ f.Valid A label D) ∧
      PrivatelyEquivalent A label E (f.result label C) (f.result label D) := by
  obtain ⟨π, priv, same⟩ := h
  have fixed : f.rename π = f := f.rename_eq_self fun o member => priv.fixes o (named member)
  refine ⟨?_, π, priv, ?_⟩
  · have valid := valid_renamed priv.keeps same f
    rw [fixed] at valid
    exact valid.symm
  · have result := result_renamed priv.keeps same f
    rwa [fixed] at result

/-- **Runs that name only escaped identities keep the equivalence.** -/
theorem named_run {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D)
    {w : List (Firing T S O)} (named : ∀ f ∈ w, f.names ⊆ E) :
    (Executable A label C w ↔ Executable A label D w) ∧
      PrivatelyEquivalent A label E (follow label C w) (follow label D w) := by
  obtain ⟨π, priv, same⟩ := h
  have fixed : w.map (Firing.rename π) = w := list_map_eq_self fun f member =>
    f.rename_eq_self fun o inNames => priv.fixes o (named f member inNames)
  refine ⟨?_, π, priv, ?_⟩
  · calc Executable A label C w
        ↔ Executable A label (renameConfiguration π C) (w.map (Firing.rename π)) :=
          (executable_rename A priv.keeps C w).symm
      _ ↔ Executable A label (renameConfiguration π C) w := by rw [fixed]
      _ ↔ Executable A label D w := executable_congr A label w same
  · have moved := follow_rename (label := label) priv.keeps C w
    rw [fixed] at moved
    rw [← moved]
    exact follow_congr A label w same

end PrivatelyEquivalent

end Firings

/-! ## Clients respect private equivalence -/

/-- **A probe of a client**: whether a held reference is present, a predicate query asked at every
solution of the knowledge, or a guard (an equation, an absence or a count) asked at every
solution. -/
inductive Probe (T : Type uT) (S : Type uS) (O : Type uO) where
  | present (reference : O)
  | ask (query : PredicateQueryAdmission.Query T S O)
  | check (guard : Check T)

namespace Probe

/-- The identities a probe names: the reference, or the identities the query claims to have seen. -/
def names : Probe T S O → Finset O
  | present reference => {reference}
  | ask query => query.seen
  | check _ => ∅

/-- Rename the identities a probe names. -/
def rename (π : O ≃ O) : Probe T S O → Probe T S O
  | present reference => present (π reference)
  | ask query => ask (renameQuery π query)
  | check guard => check guard

variable (A : SubstitutionAction T S) (label : O → T)

/-- **What a probe observes at a configuration.** -/
def Observes : Probe T S O → Configuration T O → Prop
  | present reference, C => reference ∈ C.present
  | ask query, C => query.Ask A C.equations label C.present
  | check guard, C => A.Entails C.equations fun σ => guard.Holds A σ label C.present

variable {A label}

omit [DecidableEq O] in
/-- **Probes are equivariant** under label-keeping renamings. -/
theorem observes_rename {π : O ≃ O} (keeps : ∀ o, label (π o) = label o) (p : Probe T S O)
    (C : Configuration T O) :
    (p.rename π).Observes A label (renameConfiguration π C) ↔ p.Observes A label C := by
  cases p with
  | present reference => exact Finset.mem_map' π.toEmbedding
  | ask query =>
      exact forall_congr' fun σ => imp_congr_right fun _ => queryHolds_rename keeps σ C.present query
  | check guard =>
      exact forall_congr' fun σ => imp_congr_right fun _ => holds_rename A keeps σ C.present guard

omit [DecidableEq O] in
/-- Probes see configurations only up to the solutions of their knowledge. -/
theorem observes_congr (p : Probe T S O) {C D : Configuration T O} (same : SameUpTo A C D) :
    p.Observes A label C ↔ p.Observes A label D := by
  obtain ⟨equivalent, present⟩ := same
  cases p with
  | present reference =>
      show reference ∈ C.present ↔ reference ∈ D.present
      rw [present]
  | ask query =>
      show (∀ σ, A.Models σ C.equations → _) ↔ (∀ σ, A.Models σ D.equations → _)
      rw [present]
      exact forall_congr' fun σ => imp_congr_left (equivalent σ)
  | check guard =>
      show (∀ σ, A.Models σ C.equations → _) ↔ (∀ σ, A.Models σ D.equations → _)
      rw [present]
      exact forall_congr' fun σ => imp_congr_left (equivalent σ)

omit [DecidableEq O] in
/-- A probe that names only fixed identities is its own renaming. -/
theorem rename_eq_self (p : Probe T S O) {π : O ≃ O} (fixes : ∀ o ∈ p.names, π o = o) :
    p.rename π = p := by
  cases p with
  | present reference =>
      show present (π reference) = present reference
      rw [fixes reference (Finset.mem_singleton_self reference)]
  | ask query =>
      show ask (⟨query.region, query.seen.map π.toEmbedding⟩ : PredicateQueryAdmission.Query T S O) =
        ask query
      rw [finset_map_eq_self (s := query.seen) π fixes]
  | check guard => rfl

end Probe

namespace PrivatelyEquivalent

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

omit [DecidableEq O] in
/-- **Clients respect private equivalence**: a probe that names only escaped identities observes
the same at privately equivalent states. -/
theorem observes {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D)
    {p : Probe T S O} (named : p.names ⊆ E) : p.Observes A label C ↔ p.Observes A label D := by
  obtain ⟨π, priv, same⟩ := h
  have fixed : p.rename π = p := p.rename_eq_self fun o member => priv.fixes o (named member)
  calc p.Observes A label C
      ↔ (p.rename π).Observes A label (renameConfiguration π C) :=
        (Probe.observes_rename priv.keeps p C).symm
    _ ↔ p.Observes A label (renameConfiguration π C) := by rw [fixed]
    _ ↔ p.Observes A label D := Probe.observes_congr p same

omit [DecidableEq O] in
/-- **Answers of predicate queries**: at privately equivalent states, the identities in a query's
region agree on every escaped identity, and their numbers agree; the private ones are renamed. -/
theorem answer {C D : Configuration T O} (h : PrivatelyEquivalent A label E C D)
    (region : T → Bool) :
    (∀ o ∈ E, o ∈ regionOf label C.present region ↔ o ∈ regionOf label D.present region) ∧
      (regionOf label C.present region).card = (regionOf label D.present region).card := by
  obtain ⟨π, priv, same⟩ := h
  have moved : regionOf label D.present region = (regionOf label C.present region).map π.toEmbedding := by
    rw [← same.2]
    exact regionOf_rename priv.keeps C.present region
  rw [moved]
  exact ⟨fun o escaped => (priv.mem_map_iff escaped _).symm, (Finset.card_map _).symm⟩

end PrivatelyEquivalent

namespace Client

variable {A : SubstitutionAction T S} {label : O → T}

/-- **A permitted probe of a client** names only identities the client has: references it holds,
identities it sighted, recorded or saw published. -/
def Permits (c : Client O) (p : Probe T S O) : Prop := p.names ⊆ c.escaped

/-- **Every permitted client observes the same at states equivalent for it.** -/
theorem respects (c : Client O) {C D : Configuration T O}
    (h : PrivatelyEquivalent A label c.escaped C D) {p : Probe T S O} (permitted : c.Permits p) :
    p.Observes A label C ↔ p.Observes A label D :=
  h.observes permitted

/-- A held reference is a permitted probe. -/
theorem permits_present (c : Client O) {o : O} (held : o ∈ c.held) :
    c.Permits (Probe.present o : Probe T S O) := by
  intro x member
  simp only [Probe.names, Finset.mem_singleton] at member
  rw [member]
  exact c.held_escaped held

/-- Guards name no identity and are always permitted. -/
theorem permits_check (c : Client O) (guard : Check T) : c.Permits (.check guard : Probe T S O) := by
  intro x member
  simp [Probe.names] at member

end Client

/-! ## Joint ends -/

section Joint

variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O)

/-- **Equivalence of joint ends**: a state with the client context its history left. One private
renaming, fixing the identities `E` public before the comparison, relates the states and the client
contexts. -/
def JointEquivalent (x y : Configuration T O × Client O) : Prop :=
  ∃ π : O ≃ O, PrivateRenaming label E π ∧ SameUpTo A (renameConfiguration π x.1) y.1 ∧
    x.2.rename π = y.2

variable {A label E}

omit [DecidableEq O] in
theorem JointEquivalent.refl (x : Configuration T O × Client O) : JointEquivalent A label E x x :=
  ⟨Equiv.refl O, .refl, by rw [renameConfiguration_refl]; exact SameUpTo.refl A x.1,
    Client.rename_refl x.2⟩

omit [DecidableEq O] in
theorem JointEquivalent.symm {x y : Configuration T O × Client O}
    (h : JointEquivalent A label E x y) : JointEquivalent A label E y x := by
  obtain ⟨π, priv, same, clients⟩ := h
  refine ⟨π.symm, priv.symm, ?_, ?_⟩
  · have back := sameUpTo_rename A π.symm same
    rw [← renameConfiguration_trans, Equiv.self_trans_symm, renameConfiguration_refl] at back
    exact sameUpTo_symm A back
  · rw [← clients, ← Client.rename_trans, Equiv.self_trans_symm, Client.rename_refl]

omit [DecidableEq O] in
theorem JointEquivalent.trans {x y z : Configuration T O × Client O}
    (h : JointEquivalent A label E x y) (k : JointEquivalent A label E y z) :
    JointEquivalent A label E x z := by
  obtain ⟨π, priv, same, clients⟩ := h
  obtain ⟨ρ, priv', same', clients'⟩ := k
  refine ⟨π.trans ρ, priv.trans priv', ?_, ?_⟩
  · rw [renameConfiguration_trans]
    exact GuardFreeProcessOrders.SameUpTo.trans A (sameUpTo_rename A ρ same) same'
  · rw [Client.rename_trans, clients, clients']

/-- **For one client whose identities are all fixed, joint equivalence is private equivalence.** -/
theorem jointEquivalent_iff (c : Client O) (fixed : c.escaped ⊆ E) (C D : Configuration T O) :
    JointEquivalent A label E (C, c) (D, c) ↔ PrivatelyEquivalent A label E C D := by
  constructor
  · rintro ⟨π, priv, same, -⟩
    exact ⟨π, priv, same⟩
  · rintro ⟨π, priv, same⟩
    exact ⟨π, priv, same, c.rename_eq_self fun o member => priv.fixes o (fixed member)⟩

omit [DecidableEq O] in
/-- Joint equivalence forgets the client context to private equivalence of the states. -/
theorem JointEquivalent.states {x y : Configuration T O × Client O}
    (h : JointEquivalent A label E x y) : PrivatelyEquivalent A label E x.1 y.1 := by
  obtain ⟨π, priv, same, -⟩ := h
  exact ⟨π, priv, same⟩

omit [DecidableEq O] in
/-- Equivalent joint ends recorded the same number of identities as evidence. -/
theorem JointEquivalent.evidence_card {x y : Configuration T O × Client O}
    (h : JointEquivalent A label E x y) : x.2.evidence.card = y.2.evidence.card := by
  obtain ⟨π, -, -, clients⟩ := h
  rw [← clients]
  exact (Finset.card_map _).symm

end Joint

/-! ## Alternatives under fresh names -/

section Alternatives

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

theorem swap_keeps {r r' : O} (same : label r' = label r) :
    ∀ o, label (Equiv.swap r r' o) = label o := by
  intro o
  by_cases isR : o = r
  · subst isR
    rw [Equiv.swap_apply_left, same]
  · by_cases isR' : o = r'
    · subst isR'
      rw [Equiv.swap_apply_right, same]
    · rw [Equiv.swap_apply_of_ne_of_ne isR isR']

variable {f : Firing T S O} {C : Configuration T O} {r r' : O}

theorem made_fresh (valid : f.Valid A label C) (made : r ∈ f.selection.made) : r ∉ C.present :=
  Finset.disjoint_left.mp valid.firing.occurrences.fresh (by simpa [Selection.commit] using made)

theorem swap_fixes_state (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) : renameConfiguration (Equiv.swap r r') C = C := by
  obtain ⟨equations, present⟩ := C
  show (⟨equations, present.map (Equiv.swap r r').toEmbedding⟩ : Configuration T O) = ⟨equations, present⟩
  rw [finset_map_eq_self _ fun o member => Equiv.swap_apply_of_ne_of_ne
    (fun isR => made_fresh valid made (by rw [← isR]; exact member))
    (fun isR' => absent (by rw [← isR']; exact member))]

/-- **The alternative under a fresh name is admitted at the same state.** -/
theorem fresh_alternative_valid (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) :
    (f.rename (Equiv.swap r r')).Valid A label C := by
  have admitted := (Firing.valid_rename A (swap_keeps same) f C).mpr valid
  rwa [swap_fixes_state valid made absent] at admitted

/-- **Its result is the renamed result.** -/
theorem fresh_alternative_result (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) :
    (f.rename (Equiv.swap r r')).result label C =
      renameConfiguration (Equiv.swap r r') (f.result label C) := by
  have result := Firing.result_rename (swap_keeps same) f C
  rwa [swap_fixes_state valid made absent] at result

/-- **Unseen fresh names interfere**: for every set of escaped identities containing neither name,
the original's result and the alternative's are privately equivalent. -/
theorem fresh_alternative_equivalent (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) (unseen : r ∉ E) (unseen' : r' ∉ E) :
    PrivatelyEquivalent A label E (f.result label C) ((f.rename (Equiv.swap r r')).result label C) := by
  refine ⟨Equiv.swap r r', ⟨swap_keeps same, fun o escaped => ?_⟩, ?_⟩
  · exact Equiv.swap_apply_of_ne_of_ne (fun isR => unseen (isR ▸ escaped))
      (fun isR' => unseen' (isR' ▸ escaped))
  · rw [fresh_alternative_result valid made absent same]
    exact SameUpTo.refl A _

theorem result_present_iff {o : O} :
    o ∈ (f.result label C).present ↔ (o ∈ C.present ∧ o ∉ f.selection.taken) ∨ o ∈ f.selection.made := by
  show o ∈ fire C.present (f.selection.commit (T := T)) ↔ _
  simp [MeTTaCalculus.OccurrenceCommits.mem_fire, Selection.commit]

/-- **A seen fresh name records the alternative**: a client holding `r` separates the original's
result from the alternative's when `r'` is new to the firing. -/
theorem fresh_alternative_separated (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) (new : r' ∉ f.names) (seen : r ∈ E) :
    ¬ PrivatelyEquivalent A label E (f.result label C) ((f.rename (Equiv.swap r r')).result label C) := by
  intro h
  have here : r ∈ (f.result label C).present := result_present_iff.mpr (Or.inr made)
  have there := (h.escaped_iff seen).mp here
  rw [fresh_alternative_result valid made absent same] at there
  obtain ⟨a, member, moved⟩ := Finset.mem_map.mp there
  have isR' : a = r' := by
    rw [Equiv.coe_toEmbedding, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at moved
    exact moved
  rw [isR'] at member
  have notMade : r' ∉ f.selection.made := fun inMade => new (by simp [Firing.names, inMade])
  rcases result_present_iff.mp member with ⟨present, -⟩ | inMade
  · exact absent present
  · exact notMade inMade

end Alternatives

/-! ## Controls -/

namespace ObservationControls

open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)

/-- A state whose single row is `o`, with empty knowledge. -/
def row (o : ℕ) : Configuration (Mettapedia.Logic.LP.Term ConstraintMultisetRewriting.Controls.signature) ℕ :=
  ⟨[], {o}⟩

theorem label_20 : label 20 = label 21 := rfl

theorem rows_keeps : ∀ o, label (Equiv.swap 20 21 o) = label o := swap_keeps rfl

/-- **Rows nobody has seen are interchangeable.** -/
theorem private_rows : PrivatelyEquivalent A label ∅ (row 20) (row 21) := by
  refine ⟨Equiv.swap 20 21, ⟨rows_keeps, fun o member => absurd member (Finset.notMem_empty o)⟩,
    fun _ => Iff.rfl, ?_⟩
  show ({20} : Finset ℕ).map (Equiv.swap 20 21).toEmbedding = {21}
  rw [Finset.map_singleton]
  rfl

/-- The client that holds a reference to the row `20`. -/
def holder : Client ℕ := ⟨[20], ∅, ∅, ∅⟩

/-- **A client holding a reference separates the rows.** -/
theorem held_reference_separates : ¬ PrivatelyEquivalent A label holder.escaped (row 20) (row 21) := by
  intro h
  have seen := (holder.respects h (holder.permits_present (o := 20) (by simp [holder]))).mp
    (show (20 : ℕ) ∈ ({20} : Finset ℕ) by decide)
  exact absurd (show (20 : ℕ) ∈ ({21} : Finset ℕ) from seen) (by decide)

/-- **The forget-all end is not respected by a client holding a reference**: the two states have
the same knowledge and the same bag of labels, everything the forget-all end keeps, and the client
holding `20` separates them. -/
theorem forget_all_not_respected :
    (row 20).equations = (row 21).equations ∧
      (row 20).present.val.map label = (row 21).present.val.map label ∧
      PrivatelyEquivalent A label ∅ (row 20) (row 21) ∧
      ¬ PrivatelyEquivalent A label holder.escaped (row 20) (row 21) :=
  ⟨rfl, rfl, private_rows, held_reference_separates⟩

/-- **Swapping an escaped identity with a private one is not private.** -/
theorem swap_escaped_not_private :
    (∀ o, label (Equiv.swap 20 22 o) = label o) ∧
      ¬ PrivateRenaming label holder.escaped (Equiv.swap 20 22) := by
  refine ⟨swap_keeps rfl, fun priv => ?_⟩
  have fixed := priv.fixes 20 (by simp [holder, Client.escaped])
  rw [Equiv.swap_apply_left] at fixed
  exact absurd fixed (by decide)

/-- **The states it relates are separated by the client.** -/
theorem escaped_swap_separated :
    SameUpTo A (renameConfiguration (Equiv.swap 20 22) (row 20)) (row 22) ∧
      ¬ PrivatelyEquivalent A label holder.escaped (row 20) (row 22) := by
  refine ⟨⟨fun _ => Iff.rfl, ?_⟩, fun h => ?_⟩
  · show ({20} : Finset ℕ).map (Equiv.swap 20 22).toEmbedding = {22}
    rw [Finset.map_singleton]
    rfl
  · have seen := (holder.respects h (holder.permits_present (o := 20) (by simp [holder]))).mp
      (show (20 : ℕ) ∈ ({20} : Finset ℕ) by decide)
    exact absurd (show (20 : ℕ) ∈ ({22} : Finset ℕ) from seen) (by decide)

/-- **One occurrence referenced twice is not two occurrences**: no renaming turns the references
`[20, 20]` into `[20, 21]`. -/
theorem shared_not_copied : ¬ ∃ π : ℕ ≃ ℕ, [20, 20].map π = [20, 21] := by
  rintro ⟨π, moved⟩
  have shared := (sharing_rename π [20, 20] 0 1).mpr rfl
  rw [moved] at shared
  exact absurd shared (by decide)

/-- **Multiplicity matters**: one row is not equivalent to two rows of the same label, even for a
client that has seen nothing. -/
theorem copied_not_equivalent :
    ¬ PrivatelyEquivalent A label ∅ (row 20) ⟨[], {20, 21}⟩ := by
  intro h
  have counts : ({20} : Finset ℕ).card = ({20, 21} : Finset ℕ).card := h.card_eq
  rw [Finset.card_singleton, Finset.card_pair (by decide)] at counts
  exact absurd counts (by decide)

/-- The state after a record was consumed into the row `30`. -/
def erased : Configuration (Mettapedia.Logic.LP.Term ConstraintMultisetRewriting.Controls.signature) ℕ :=
  ⟨[], {30}⟩

/-- **A record that escaped into evidence outlives its row**: two histories end in the same state,
one after recording its row `20` as evidence and consuming it, the other without a record; their
states are equivalent, and their joint ends are not. -/
theorem evidence_outlives_record :
    PrivatelyEquivalent A label ∅ erased erased ∧
      ¬ JointEquivalent A label ∅ (erased, ⟨[], ∅, {20}, ∅⟩) (erased, ⟨[], ∅, ∅, ∅⟩) := by
  refine ⟨PrivatelyEquivalent.refl erased, fun h => ?_⟩
  have counts : ({20} : Finset ℕ).card = (∅ : Finset ℕ).card := h.evidence_card
  rw [Finset.card_singleton, Finset.card_empty] at counts
  exact absurd counts (by decide)

/-- **A record of a fresh name alone is relative to what was public before.** Two histories that
each recorded their own fresh row as evidence and then consumed it have equivalent joint ends when
neither row was public before: one swap relates the ledgers. Once the row `20` was public before,
the ledgers are told apart. -/
theorem fresh_records_relative :
    JointEquivalent A label ∅ (erased, ⟨[], ∅, {20}, ∅⟩) (erased, ⟨[], ∅, {21}, ∅⟩) ∧
      ¬ JointEquivalent A label {20} (erased, ⟨[], ∅, {20}, ∅⟩) (erased, ⟨[], ∅, {21}, ∅⟩) := by
  refine ⟨⟨Equiv.swap 20 21, ⟨rows_keeps, fun o member => absurd member (Finset.notMem_empty o)⟩,
    ⟨fun _ => Iff.rfl, ?_⟩, ?_⟩, ?_⟩
  · show ({30} : Finset ℕ).map (Equiv.swap 20 21).toEmbedding = {30}
    rw [Finset.map_singleton]
    rfl
  · simp [Client.rename, Finset.map_singleton, Equiv.swap_apply_left]
  · rintro ⟨π, priv, -, clients⟩
    have fixed := priv.fixes 20 (Finset.mem_singleton_self 20)
    have ledger := congrArg Client.evidence clients
    simp only [Client.rename, Finset.map_singleton, Equiv.coe_toEmbedding, fixed] at ledger
    rw [Finset.singleton_inj] at ledger
    exact absurd ledger (by decide)

end ObservationControls

#print axioms list_map_eq_self
#print axioms finset_map_eq_self
#print axioms mem_sighted
#print axioms mem_runSighted
#print axioms Client.watch_escaped
#print axioms Client.rename_trans
#print axioms Client.rename_eq_self
#print axioms PrivateRenaming.symm
#print axioms PrivateRenaming.trans
#print axioms PrivateRenaming.mem_map_iff
#print axioms renameConfiguration_trans
#print axioms sameUpTo_rename
#print axioms labels_rename
#print axioms sharing_rename
#print axioms PrivatelyEquivalent.symm
#print axioms PrivatelyEquivalent.trans
#print axioms PrivatelyEquivalent.mono
#print axioms PrivatelyEquivalent.labels_eq
#print axioms PrivatelyEquivalent.card_eq
#print axioms PrivatelyEquivalent.escaped_iff
#print axioms classSetoid
#print axioms privateEnd_eq_iff
#print axioms Firing.rename_eq_self
#print axioms valid_renamed
#print axioms result_renamed
#print axioms PrivatelyEquivalent.firing
#print axioms PrivatelyEquivalent.named_firing
#print axioms PrivatelyEquivalent.named_run
#print axioms Probe.observes_rename
#print axioms Probe.observes_congr
#print axioms Probe.rename_eq_self
#print axioms PrivatelyEquivalent.observes
#print axioms PrivatelyEquivalent.answer
#print axioms Client.respects
#print axioms JointEquivalent.symm
#print axioms JointEquivalent.trans
#print axioms jointEquivalent_iff
#print axioms fresh_alternative_valid
#print axioms fresh_alternative_result
#print axioms fresh_alternative_equivalent
#print axioms fresh_alternative_separated
#print axioms ObservationControls.private_rows
#print axioms ObservationControls.held_reference_separates
#print axioms ObservationControls.forget_all_not_respected
#print axioms ObservationControls.swap_escaped_not_private
#print axioms ObservationControls.escaped_swap_separated
#print axioms ObservationControls.shared_not_copied
#print axioms ObservationControls.copied_not_equivalent
#print axioms ObservationControls.evidence_outlives_record
#print axioms ObservationControls.fresh_records_relative

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
