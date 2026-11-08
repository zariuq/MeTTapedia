import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority

/-!
# Attenuation as a program

Two attenuated handles are written as rules over fresh space names, with no rights primitive.

* **Send-only.** The holder gets a fresh name `m`; the owner installs the forwarder
  "take `X` at `m`, make `X` at `n`". Posting `q` at `m` and forwarding it ends with the same
  occurrences as the primitive send of `q` at `n`, with the forwarded identity in place of the
  primitive's, nothing left at `m`, a store that refines the primitive's, and every check agreeing
  under every solution of the program's store (`forwarder_faithful`). When the forwarder's variable
  is fresh for an observation, every check is entailed after the forwarding exactly when it is
  entailed after the primitive send (`forwarder_observations_agree`, with a concrete instance
  `Controls.forwarded_count_entailed`). The primitive send is the
  rigid model's `send`-formed firing (`send_is_rigid_send`, `rigid_send_formed_iff`). By the
  authority theorems the holder of `m` alone cannot take or read at `n`
  (`Controls.mailbox_holder_cannot_take_at_owner_store`).
* **Read-only, "ask the owner".** The asker posts an ask at its own fresh name `m`; the owner's
  server takes it, reads at `n` with the asker's pattern, and replies at `m`; the asker collects.
  For the principal instance of the server (its pattern is the asker's), the three firings run
  exactly when the primitive read runs, and end with the same occurrences and an equivalent store,
  in which the asker's pattern equals the row read: sequential existence, and answers as data
  (`ask_faithful_fragment`).

## Where the programs differ from the primitives (separating examples, `Controls`)

* **Read-before-take.** A primitive read must precede the owner's take of the row it reads
  (`peek_impossible_after_owner_take`); the asker's acting step can follow it
  (`ask_acts_after_owner_take`).
* **Absence.** A primitive absence check refuses to act once a matching row is present
  (`guarded_act_refused_when_present`); the asker's acting step, relying on the server's earlier
  answer, acts in that configuration (`ask_absence_acts_when_present`).
* **Copies.** Two asks served from one row leave two reply occurrences at the asker's space while
  the owner holds one row (`two_asks_two_copies`); a read leaves no copy.
* **Atomicity.** The forwarder is a second firing. An observer that orders itself after the
  client's signal sees the letter missing at `n` (`forwarder_gap_observable`); after the primitive
  send it cannot (`primitive_send_no_gap`).
* **Shared forwarder names.** Two holders of one name `m` have full authority over `m`: one takes
  the other's post (`shared_mailbox_intercepted`). With one fresh name per holder the other has no
  name for it and the post stays (`separate_mailbox_not_intercepted`).
* **Reads write bindings.** A read port equation binds an open variable of the stored row, for the
  primitive read and for the server's read alike (`peek_binds_owner_variable`): read-only access
  in the two-way step is not read-only on the store unless stored rows are ground.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes (Rights Facet)

universe uT uS uN uO

/-! ## Observations of one exchanged occurrence -/

section Observation

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {A : SubstitutionAction T S}

/-- Exchanging one occurrence for another whose label agrees under a solution changes no check. -/
theorem holds_insert_congr {σ : S} {label : O → T} {P : Finset O} {x y : O} (hx : x ∉ P)
    (hy : y ∉ P) (same : A.E (A.apply σ (label x)) (A.apply σ (label y))) :
    ∀ check : Check T, check.Holds A σ label (insert x P) ↔ check.Holds A σ label (insert y P)
  | .equal _ _ => Iff.rfl
  | .absent p => by
      simp only [Check.Holds, Finset.forall_mem_insert]
      constructor
      · rintro ⟨notX, rest⟩
        exact ⟨fun matchY => notX (A.equivalence.trans matchY (A.equivalence.symm same)), rest⟩
      · rintro ⟨notY, rest⟩
        exact ⟨fun matchX => notY (A.equivalence.trans matchX same), rest⟩
  | .count p k => by
      classical
      have matching : A.E (A.apply σ p) (A.apply σ (label x)) ↔
          A.E (A.apply σ p) (A.apply σ (label y)) :=
        ⟨fun h => A.equivalence.trans h same,
          fun h => A.equivalence.trans h (A.equivalence.symm same)⟩
      simp only [Check.Holds, Check.matches]
      rw [Finset.filter_insert, Finset.filter_insert]
      by_cases hX : A.E (A.apply σ p) (A.apply σ (label x))
      · have hY := matching.mp hX
        rw [if_pos hX, if_pos hY,
          Finset.card_insert_of_notMem (fun member => hx (Finset.mem_filter.mp member).1),
          Finset.card_insert_of_notMem (fun member => hy (Finset.mem_filter.mp member).1)]
      · have hY : ¬ A.E (A.apply σ p) (A.apply σ (label y)) := fun h => hX (matching.mpr h)
        rw [if_neg hX, if_neg hY]

/-- The terms a check reads. -/
def checkTerms {T : Type uT} : Check T → List T
  | .equal l r => [l, r]
  | .absent p => [p]
  | .count p _ => [p]

omit [DecidableEq O] in
/-- **A check's verdict depends only on the solution's reading of its terms and of the present
labels.** -/
theorem holds_congr {σ τ : S} {label : O → T} {P : Finset O} :
    ∀ check : Check T, (∀ t ∈ checkTerms check, A.E (A.apply τ t) (A.apply σ t)) →
      (∀ o ∈ P, A.E (A.apply τ (label o)) (A.apply σ (label o))) →
      (check.Holds A τ label P ↔ check.Holds A σ label P)
  | .equal l r, terms, _ => by
      have left := terms l (by simp [checkTerms])
      have right := terms r (by simp [checkTerms])
      simp only [Check.Holds, SubstitutionAction.Solves]
      constructor
      · intro same
        exact A.equivalence.trans (A.equivalence.symm left) (A.equivalence.trans same right)
      · intro same
        exact A.equivalence.trans left (A.equivalence.trans same (A.equivalence.symm right))
  | .absent p, terms, labels => by
      have pattern := terms p (by simp [checkTerms])
      simp only [Check.Holds]
      constructor
      · intro none o present matching
        exact none o present (A.equivalence.trans pattern
          (A.equivalence.trans matching (A.equivalence.symm (labels o present))))
      · intro none o present matching
        exact none o present (A.equivalence.trans (A.equivalence.symm pattern)
          (A.equivalence.trans matching (labels o present)))
  | .count p k, terms, labels => by
      have pattern := terms p (by simp [checkTerms])
      classical
      simp only [Check.Holds]
      have regions : Check.matches A τ label P p = Check.matches A σ label P p := by
        ext o
        simp only [Check.matches, Finset.mem_filter]
        constructor
        · rintro ⟨present, matching⟩
          exact ⟨present, A.equivalence.trans (A.equivalence.symm pattern)
            (A.equivalence.trans matching (labels o present))⟩
        · rintro ⟨present, matching⟩
          exact ⟨present, A.equivalence.trans pattern
            (A.equivalence.trans matching (A.equivalence.symm (labels o present)))⟩
      rw [regions]

end Observation

/-! ## Send-only: the forwarder -/

section Forwarder

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} (sts : SpaceTerms A N)

/-- Make one payload at one space. -/
def sendRule (s q : T) : LocatedRule T := ⟨[], [], [], [], [(s, q)]⟩

/-- **The forwarder**: take a payload at `m`, make it at `n`. -/
def forwarder (m n X : T) : LocatedRule T := ⟨[(m, X)], [], [], [], [(n, X)]⟩

/-- Make one fresh occurrence. -/
def makeOne (o : O) : Selection O := ⟨[], [], [o]⟩

/-- Take one occurrence, make one fresh occurrence. -/
def moveOne (o o' : O) : Selection O := ⟨[o], [], [o']⟩

/-- The configuration after a send. -/
def sentAt (label : O → T) (s q : T) (o : O) (C : Configuration T O) : Configuration T O :=
  (makeOne o).result label ((sendRule s q).toRule sts) C

/-- The configuration after a post at `m` and its forwarding to `n`. -/
def forwardedAt (label : O → T) (m n q X : T) (o1 o2 : O) (C : Configuration T O) :
    Configuration T O :=
  (moveOne o1 o2).result label ((forwarder m n X).toRule sts) (sentAt sts label m q o1 C)

variable {sts}

theorem sentAt_equations (label : O → T) (s q : T) (o : O) (C : Configuration T O) :
    (sentAt sts label s q o C).equations = C.equations := by
  simp [sentAt, Selection.result, Selection.problem, Selection.equations, makeOne, sendRule,
    LocatedRule.toRule]

theorem sentAt_present (label : O → T) (s q : T) (o : O) (C : Configuration T O) :
    (sentAt sts label s q o C).present = insert o C.present := by
  ext x
  simp [sentAt, Selection.result, fire, Selection.commit, makeOne]

theorem send_valid_iff {label : O → T} {s q : T} {o : O} (labelO : label o = sts.atSpace s q)
    (C : Configuration T O) :
    (makeOne o).Valid A label ((sendRule s q).toRule sts) C ↔
      A.Consistent C.equations ∧ o ∉ C.present := by
  have problem : (makeOne o).problem label ((sendRule s q).toRule sts) C = C.equations := by
    simp [Selection.problem, Selection.equations, makeOne, sendRule, LocatedRule.toRule]
  constructor
  · intro valid
    refine ⟨problem ▸ valid.consistent, ?_⟩
    simpa [Selection.commit, makeOne] using valid.occurrences.fresh
  · rintro ⟨consistent, fresh⟩
    refine ⟨by simp [makeOne], by simp [makeOne], rfl, rfl, ?_, ?_, problem ▸ consistent, ?_⟩
    · simp [makeOne, sendRule, LocatedRule.toRule, place, labelO]
    · exact ⟨by simp [Selection.commit, makeOne], by simp [Selection.commit, makeOne],
        by simp [Selection.commit, makeOne], by simpa [Selection.commit, makeOne] using fresh,
        by simp [Selection.commit]⟩
    · simp [sendRule, LocatedRule.toRule]

theorem forward_valid_iff {label : O → T} {m n X q : T} {o1 o2 : O}
    (labelO1 : label o1 = sts.atSpace m q) (labelO2 : label o2 = sts.atSpace n X)
    (C : Configuration T O) (present : o1 ∈ C.present) :
    (moveOne o1 o2).Valid A label ((forwarder m n X).toRule sts) C ↔
      A.Consistent (C.equations ++ [(sts.atSpace m X, sts.atSpace m q)]) ∧ o2 ∉ C.present := by
  have problem : (moveOne o1 o2).problem label ((forwarder m n X).toRule sts) C =
      C.equations ++ [(sts.atSpace m X, sts.atSpace m q)] := by
    simp [Selection.problem, Selection.equations, moveOne, forwarder, LocatedRule.toRule, place,
      labelO1]
  constructor
  · intro valid
    exact ⟨problem ▸ valid.consistent,
      by simpa [Selection.commit, moveOne] using valid.occurrences.fresh⟩
  · rintro ⟨consistent, fresh⟩
    refine ⟨by simp [moveOne], by simp [moveOne], rfl, rfl, ?_, ?_, problem ▸ consistent, ?_⟩
    · simp [moveOne, forwarder, LocatedRule.toRule, place, labelO2]
    · exact ⟨by simpa [Selection.commit, moveOne] using present,
        by simp [Selection.commit, moveOne], by simp [Selection.commit, moveOne],
        by simpa [Selection.commit, moveOne] using fresh, by simp [Selection.commit]⟩
    · simp [forwarder, LocatedRule.toRule]

theorem solves_place_iff (σ : S) (m : N) (X q : T) :
    A.Solves σ (sts.atSpace (sts.name m) X, sts.atSpace (sts.name m) q) ↔ A.Solves σ (X, q) := by
  simp only [SubstitutionAction.Solves, sts.apply_atSpace, sts.apply_name, sts.E_atSpace]
  exact ⟨fun same => same.2, fun same => ⟨A.equivalence.refl _, same⟩⟩

/-- **The forwarder is faithful to the primitive send at `n`.** Both runs execute; they end with
the same occurrences up to the forwarded identity, with nothing left at `m`; the program's store
refines the primitive's; and under every solution of the program's store every check (equality,
absence, count, at any space) agrees between the two final configurations. The hypothesis
`free` says the forwarder's variable may take the posted payload. -/
theorem forwarder_faithful {label : O → T} {m n : N} {q X : T} {o o1 o2 : O}
    (labelO : label o = sts.atSpace (sts.name n) q)
    (labelO1 : label o1 = sts.atSpace (sts.name m) q)
    (labelO2 : label o2 = sts.atSpace (sts.name n) X)
    {C : Configuration T O} (freshO : o ∉ C.present) (fresh1 : o1 ∉ C.present)
    (fresh2 : o2 ∉ C.present) (distinct : o2 ≠ o1)
    (free : A.Consistent (C.equations ++ [(X, q)])) :
    (makeOne o).Valid A label ((sendRule (sts.name n) q).toRule sts) C ∧
      (makeOne o1).Valid A label ((sendRule (sts.name m) q).toRule sts) C ∧
      (moveOne o1 o2).Valid A label ((forwarder (sts.name m) (sts.name n) X).toRule sts)
        (sentAt sts label (sts.name m) q o1 C) ∧
      (sentAt sts label (sts.name n) q o C).present = insert o C.present ∧
      (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).present =
        insert o2 C.present ∧
      A.Refines (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).equations
        (sentAt sts label (sts.name n) q o C).equations ∧
      ∀ σ, A.Models σ (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).equations →
        ∀ check : Check T,
          check.Holds A σ label (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).present ↔
            check.Holds A σ label (sentAt sts label (sts.name n) q o C).present := by
  have consistentC : A.Consistent C.equations := by
    obtain ⟨σ, solved⟩ := free
    exact ⟨σ, ((A.models_append _ _ _).mp solved).1⟩
  have forwardedEquations :
      (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).equations =
        C.equations ++ [(sts.atSpace (sts.name m) X, sts.atSpace (sts.name m) q)] := by
    simp [forwardedAt, Selection.result, Selection.problem, Selection.equations, moveOne,
      forwarder, LocatedRule.toRule, place, labelO1, sentAt_equations]
  have forwardedPresent :
      (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).present =
        insert o2 C.present := by
    ext x
    simp only [forwardedAt, Selection.result, fire, Selection.commit, moveOne, sentAt_present,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl | old, notTaken⟩ | rfl)
      · exact absurd rfl notTaken
      · exact Or.inr old
      · exact Or.inl rfl
    · rintro (rfl | old)
      · exact Or.inr rfl
      · exact Or.inl ⟨Or.inr old, fun same => fresh1 (same ▸ old)⟩
  have postValid := (send_valid_iff labelO1 C).mpr ⟨consistentC, fresh1⟩
  refine ⟨(send_valid_iff labelO C).mpr ⟨consistentC, freshO⟩, postValid, ?_,
    sentAt_present label _ q o C, forwardedPresent, ?_, ?_⟩
  · apply (forward_valid_iff labelO1 labelO2 _ (by rw [sentAt_present]; exact Finset.mem_insert_self _ _)).mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨σ, solved⟩ := free
      refine ⟨σ, ?_⟩
      rw [sentAt_equations]
      obtain ⟨old, extra⟩ := (A.models_append _ _ _).mp solved
      refine (A.models_append _ _ _).mpr ⟨old, ?_⟩
      intro e member
      simp only [List.mem_singleton] at member
      subst member
      exact (solves_place_iff σ m X q).mpr (extra _ List.mem_cons_self)
    · rw [sentAt_present]
      simp only [Finset.mem_insert, not_or]
      exact ⟨distinct, fresh2⟩
  · intro σ solved
    rw [forwardedEquations] at solved
    rw [sentAt_equations]
    exact ((A.models_append _ _ _).mp solved).1
  · intro σ solved check
    rw [forwardedEquations] at solved
    rw [forwardedPresent, sentAt_present]
    have payloads : A.Solves σ (X, q) :=
      (solves_place_iff σ m X q).mp (((A.models_append _ _ _).mp solved).2 _ List.mem_cons_self)
    have same : A.E (A.apply σ (label o2)) (A.apply σ (label o)) := by
      rw [labelO2, labelO, sts.apply_atSpace, sts.apply_atSpace, sts.E_atSpace]
      exact ⟨A.equivalence.refl _, payloads⟩
    exact holds_insert_congr fresh2 freshO same check

/-- **Every observation of the forwarded configuration is the observation of the primitive
send.** If the forwarder's variable is fresh for an observation (every solution of the store
before extends to one where the variable is the posted payload, reading the observation's terms
and the present labels alike), the check is entailed after the forwarding exactly when it is
entailed after the primitive send. -/
theorem forwarder_observations_agree {label : O → T} {m n : N} {q X : T} {o o1 o2 : O}
    (labelO : label o = sts.atSpace (sts.name n) q)
    (labelO1 : label o1 = sts.atSpace (sts.name m) q)
    (labelO2 : label o2 = sts.atSpace (sts.name n) X)
    {C : Configuration T O} (freshO : o ∉ C.present) (fresh1 : o1 ∉ C.present)
    (fresh2 : o2 ∉ C.present) (distinct : o2 ≠ o1)
    (free : A.Consistent (C.equations ++ [(X, q)])) (check : Check T)
    (local_fresh : ∀ σ, A.Models σ C.equations → ∃ τ, A.Models τ (C.equations ++ [(X, q)]) ∧
      (∀ t ∈ checkTerms check, A.E (A.apply τ t) (A.apply σ t)) ∧
      ∀ x ∈ insert o C.present, A.E (A.apply τ (label x)) (A.apply σ (label x))) :
    A.Entails (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).equations
        (fun σ => check.Holds A σ label
          (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).present) ↔
      A.Entails (sentAt sts label (sts.name n) q o C).equations
        (fun σ => check.Holds A σ label (sentAt sts label (sts.name n) q o C).present) := by
  obtain ⟨_, _, _, sentPresent, _, refines, agree⟩ :=
    forwarder_faithful labelO labelO1 labelO2 freshO fresh1 fresh2 distinct free
  have forwardedEquations :
      (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).equations =
        C.equations ++ [(sts.atSpace (sts.name m) X, sts.atSpace (sts.name m) q)] := by
    simp [forwardedAt, Selection.result, Selection.problem, Selection.equations, moveOne,
      forwarder, LocatedRule.toRule, place, labelO1, sentAt_equations]
  constructor
  · intro entailed σ solved
    rw [sentAt_equations] at solved
    obtain ⟨τ, solvedτ, termsAgree, labelsAgree⟩ := local_fresh σ solved
    have solvedForwarded : A.Models τ
        (forwardedAt sts label (sts.name m) (sts.name n) q X o1 o2 C).equations := by
      rw [forwardedEquations]
      obtain ⟨old, extra⟩ := (A.models_append _ _ _).mp solvedτ
      refine (A.models_append _ _ _).mpr ⟨old, ?_⟩
      intro e member
      simp only [List.mem_singleton] at member
      subst member
      exact (solves_place_iff τ m X q).mpr (extra _ List.mem_cons_self)
    have holdsτ := (agree τ solvedForwarded check).mp (entailed τ solvedForwarded)
    rw [sentPresent] at holdsτ ⊢
    exact (holds_congr check termsAgree labelsAgree).mp holdsτ
  · intro entailed σ solved
    exact (agree σ solved check).mpr (entailed σ (refines σ solved))

/-- The primitive send is the rigid model's firing that makes `(n, q)`. -/
theorem send_is_rigid_send (n : N) (q : T) :
    (sendRule (sts.name n) q).toRule sts =
      (⟨[], [], [], [], [(n, q)]⟩ : RuleInstance (N × T)).map (rigid sts) := by
  simp [sendRule, LocatedRule.toRule, RuleInstance.map, place, rigid]

omit [DecidableEq O] in
/-- That firing is `send`-formed in the sense of `PublicationAuthority` exactly when the actor
holds `send` at the output's location. -/
theorem rigid_send_formed_iff (rights : Rights N) (location : O → N) (o : O) :
    PublicationAuthority.Formed rights location (makeOne o) ↔
      rights (location o) Facet.send = true := by
  simp [PublicationAuthority.Formed, makeOne]

end Forwarder

/-! ## Read-only: ask the owner -/

section AskOwner

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} (sts : SpaceTerms A N)

/-- The primitive read: read with `P` at `n`, make `Q` at `a`. -/
def peekRule (n P a Q : T) : LocatedRule T := ⟨[], [(n, P)], [], [], [(a, Q)]⟩

/-- The owner's server: take the ask at `m`, read at `n` with the asker's pattern, reply at `m`. -/
def serveRule (m ask n P reply : T) : LocatedRule T := ⟨[(m, ask)], [(n, P)], [], [], [(m, reply)]⟩

/-- The asker collects the reply at `m` and makes `Q` at `a`. -/
def collectRule (m reply a Q : T) : LocatedRule T := ⟨[(m, reply)], [], [], [], [(a, Q)]⟩

def peekSel (r o : O) : Selection O := ⟨[], [r], [o]⟩

def serveSel (o1 r o2 : O) : Selection O := ⟨[o1], [r], [o2]⟩

/-- After the ask. -/
def askedAt (label : O → T) (m ask : T) (o1 : O) (C : Configuration T O) : Configuration T O :=
  sentAt sts label m ask o1 C

/-- After the ask and the server. -/
def servedAt (label : O → T) (m ask n P reply : T) (o1 r o2 : O) (C : Configuration T O) :
    Configuration T O :=
  (serveSel o1 r o2).result label ((serveRule m ask n P reply).toRule sts)
    (askedAt sts label m ask o1 C)

/-- After the ask, the server and the collection. -/
def collectedAt (label : O → T) (m ask n P reply a Q : T) (o1 r o2 oq : O)
    (C : Configuration T O) : Configuration T O :=
  (moveOne o2 oq).result label ((collectRule m reply a Q).toRule sts)
    (servedAt sts label m ask n P reply o1 r o2 C)

/-- After the primitive read. -/
def peekedAt (label : O → T) (n P a Q : T) (r oq : O) (C : Configuration T O) :
    Configuration T O :=
  (peekSel r oq).result label ((peekRule n P a Q).toRule sts) C

variable {sts}

/-- **Ask the owner, the faithful fragment.** For the server's principal instance (its pattern is
the asker's), the ask, the server and the collection all run exactly when the primitive read runs.
They end with the same occurrences, and the program's store has the same solutions as the
primitive's: in both the asker's pattern equals the row read (answers as data). -/
theorem ask_faithful_fragment {label : O → T} {m n a P Q ask reply : T} {r o1 o2 oq : O}
    (labelO1 : label o1 = sts.atSpace m ask) (labelO2 : label o2 = sts.atSpace m reply)
    (labelOq : label oq = sts.atSpace a Q) {C : Configuration T O}
    (fresh1 : o1 ∉ C.present) (fresh2 : o2 ∉ C.present) (d12 : o1 ≠ o2) (d1q : o1 ≠ oq)
    (d2q : o2 ≠ oq) :
    ((peekSel r oq).Valid A label ((peekRule n P a Q).toRule sts) C ↔
        (makeOne o1).Valid A label ((sendRule m ask).toRule sts) C ∧
          (serveSel o1 r o2).Valid A label ((serveRule m ask n P reply).toRule sts)
            (askedAt sts label m ask o1 C) ∧
          (moveOne o2 oq).Valid A label ((collectRule m reply a Q).toRule sts)
            (servedAt sts label m ask n P reply o1 r o2 C)) ∧
      (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).present =
        (peekedAt sts label n P a Q r oq C).present ∧
      A.Equivalent (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).equations
        (peekedAt sts label n P a Q r oq C).equations ∧
      A.Entails (peekedAt sts label n P a Q r oq C).equations
        (fun σ => A.E (A.apply σ (sts.atSpace n P)) (A.apply σ (label r))) := by
  have trivialAsk : ∀ σ, A.Solves σ (sts.atSpace m ask, label o1) := by
    intro σ
    rw [labelO1]
    exact A.equivalence.refl _
  have trivialReply : ∀ σ, A.Solves σ (sts.atSpace m reply, label o2) := by
    intro σ
    rw [labelO2]
    exact A.equivalence.refl _
  have peekEquations : (peekedAt sts label n P a Q r oq C).equations =
      C.equations ++ [(sts.atSpace n P, label r)] := by
    simp [peekedAt, Selection.result, Selection.problem, Selection.equations, peekSel, peekRule,
      LocatedRule.toRule, place]
  have askedEquations : (askedAt sts label m ask o1 C).equations = C.equations :=
    sentAt_equations label m ask o1 C
  have servedEquations : (servedAt sts label m ask n P reply o1 r o2 C).equations =
      C.equations ++ [(sts.atSpace m ask, label o1)] ++ [(sts.atSpace n P, label r)] := by
    simp [servedAt, Selection.result, Selection.problem, Selection.equations, serveSel, serveRule,
      LocatedRule.toRule, place, askedEquations]
  have collectedEquations : (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).equations =
      C.equations ++ [(sts.atSpace m ask, label o1)] ++ [(sts.atSpace n P, label r)] ++
        [(sts.atSpace m reply, label o2)] := by
    simp [collectedAt, Selection.result, Selection.problem, Selection.equations, moveOne,
      collectRule, LocatedRule.toRule, place, servedEquations]
  have collectedModels : ∀ σ, A.Models σ (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).equations ↔
      A.Models σ (peekedAt sts label n P a Q r oq C).equations := by
    intro σ
    rw [collectedEquations, peekEquations]
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_cons,
      SubstitutionAction.models_nil, and_true]
    constructor
    · rintro ⟨⟨⟨old, _⟩, read⟩, _⟩
      exact ⟨old, read⟩
    · rintro ⟨old, read⟩
      exact ⟨⟨⟨old, trivialAsk σ⟩, read⟩, trivialReply σ⟩
  have askedPresent : (askedAt sts label m ask o1 C).present = insert o1 C.present :=
    sentAt_present label m ask o1 C
  have servedPresent : (servedAt sts label m ask n P reply o1 r o2 C).present =
      insert o2 C.present := by
    ext x
    simp only [servedAt, Selection.result, fire, Selection.commit, serveSel, askedPresent,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl | old, notTaken⟩ | rfl)
      · exact absurd rfl notTaken
      · exact Or.inr old
      · exact Or.inl rfl
    · rintro (rfl | old)
      · exact Or.inr rfl
      · exact Or.inl ⟨Or.inr old, fun same => fresh1 (same ▸ old)⟩
  have collectedPresent : (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).present =
      insert oq C.present := by
    ext x
    simp only [collectedAt, Selection.result, fire, Selection.commit, moveOne, servedPresent,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl | old, notTaken⟩ | rfl)
      · exact absurd rfl notTaken
      · exact Or.inr old
      · exact Or.inl rfl
    · rintro (rfl | old)
      · exact Or.inr rfl
      · exact Or.inl ⟨Or.inr old, fun same => fresh2 (same ▸ old)⟩
  have peekedPresent : (peekedAt sts label n P a Q r oq C).present = insert oq C.present := by
    ext x
    simp [peekedAt, Selection.result, fire, Selection.commit, peekSel]
  refine ⟨?_, by rw [collectedPresent, peekedPresent], collectedModels, ?_⟩
  · constructor
    · intro valid
      obtain ⟨σ, solvedPeek⟩ := valid.consistent
      have solvedFinal : A.Models σ (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).equations := by
        apply (collectedModels σ).mpr
        rw [peekEquations]
        simpa [Selection.problem, Selection.equations, peekSel, peekRule, LocatedRule.toRule,
          place] using solvedPeek
      rw [collectedEquations] at solvedFinal
      have solvedC : A.Models σ C.equations := by
        simp only [SubstitutionAction.models_append] at solvedFinal
        exact solvedFinal.1.1.1
      have rPresent : r ∈ C.present :=
        valid.occurrences.kept_subset (by simp [Selection.commit, peekSel])
      have oqFresh : oq ∉ C.present := by
        simpa [Selection.commit, peekSel] using valid.occurrences.fresh
      refine ⟨(send_valid_iff labelO1 C).mpr ⟨⟨σ, solvedC⟩, fresh1⟩, ?_, ?_⟩
      · refine ⟨by simp [serveSel], by simp [serveSel], rfl, rfl, ?_, ?_, ?_, ?_⟩
        · simp [serveSel, serveRule, LocatedRule.toRule, place, labelO2]
        · refine ⟨?_, ?_, ?_, ?_, by simp [Selection.commit]⟩
          · simp [Selection.commit, serveSel, askedPresent]
          · simp [Selection.commit, serveSel, askedPresent, rPresent]
          · simp only [Selection.commit, serveSel, List.toFinset_cons, List.toFinset_nil,
              insert_empty_eq, Finset.disjoint_singleton]
            intro same
            exact fresh1 (same ▸ rPresent)
          · simp only [Selection.commit, serveSel, askedPresent, List.toFinset_cons,
              List.toFinset_nil, insert_empty_eq, Finset.disjoint_singleton_left,
              Finset.mem_insert, not_or]
            exact ⟨fun same => d12 same.symm, fresh2⟩
        · refine ⟨σ, ?_⟩
          have : A.Models σ (C.equations ++ [(sts.atSpace m ask, label o1)] ++
              [(sts.atSpace n P, label r)]) := by
            simp only [SubstitutionAction.models_append] at solvedFinal ⊢
            exact solvedFinal.1
          simpa [Selection.problem, Selection.equations, serveSel, serveRule, LocatedRule.toRule,
            place, askedEquations] using this
        · simp [serveRule, LocatedRule.toRule]
      · refine ⟨by simp [moveOne], by simp [moveOne], rfl, rfl, ?_, ?_, ?_, ?_⟩
        · simp [moveOne, collectRule, LocatedRule.toRule, place, labelOq]
        · refine ⟨?_, by simp [Selection.commit, moveOne], by simp [Selection.commit, moveOne],
            ?_, by simp [Selection.commit]⟩
          · simp [Selection.commit, moveOne, servedPresent]
          · simp only [Selection.commit, moveOne, servedPresent, List.toFinset_cons,
              List.toFinset_nil, insert_empty_eq, Finset.disjoint_singleton_left,
              Finset.mem_insert, not_or]
            exact ⟨fun same => d2q same.symm, oqFresh⟩
        · refine ⟨σ, ?_⟩
          have : A.Models σ (C.equations ++ [(sts.atSpace m ask, label o1)] ++
              [(sts.atSpace n P, label r)] ++ [(sts.atSpace m reply, label o2)]) := solvedFinal
          simpa [Selection.problem, Selection.equations, moveOne, collectRule, LocatedRule.toRule,
            place, servedEquations] using this
        · simp [collectRule, LocatedRule.toRule]
    · rintro ⟨_, serveValid, collectValid⟩
      obtain ⟨σ, solvedCollect⟩ := collectValid.consistent
      have solvedFinal : A.Models σ (collectedAt sts label m ask n P reply a Q o1 r o2 oq C).equations := by
        rw [collectedEquations]
        simpa [Selection.problem, Selection.equations, moveOne, collectRule, LocatedRule.toRule,
          place, servedEquations] using solvedCollect
      have solvedPeek := (collectedModels σ).mp solvedFinal
      rw [peekEquations] at solvedPeek
      have rAsked : r ∈ (askedAt sts label m ask o1 C).present :=
        serveValid.occurrences.kept_subset (by simp [Selection.commit, serveSel])
      have rNotO1 : r ≠ o1 := by
        intro same
        have apart := serveValid.occurrences.apart
        simp only [Selection.commit, serveSel, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.disjoint_singleton] at apart
        exact apart same.symm
      have rPresent : r ∈ C.present := by
        rw [askedPresent, Finset.mem_insert] at rAsked
        exact rAsked.resolve_left rNotO1
      have oqFresh : oq ∉ C.present := by
        have fresh := collectValid.occurrences.fresh
        simp only [Selection.commit, moveOne, servedPresent, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.disjoint_singleton_left, Finset.mem_insert, not_or] at fresh
        exact fresh.2
      refine ⟨by simp [peekSel], by simp [peekSel], rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [peekSel, peekRule, LocatedRule.toRule, place, labelOq]
      · refine ⟨by simp [Selection.commit, peekSel], ?_, by simp [Selection.commit, peekSel],
          ?_, by simp [Selection.commit]⟩
        · simp [Selection.commit, peekSel, rPresent]
        · simpa [Selection.commit, peekSel] using oqFresh
      · exact ⟨σ, by simpa [Selection.problem, Selection.equations, peekSel, peekRule,
          LocatedRule.toRule, place] using solvedPeek⟩
      · simp [peekRule, LocatedRule.toRule]
  · intro σ solved
    rw [peekEquations] at solved
    exact ((A.models_append _ _ _).mp solved).2 _ List.mem_cons_self

end AskOwner

/-! ## Controls -/

namespace Controls

/-! ### The holder of a mailbox name cannot act at the owner's store -/

/-- The owner's store, space 7, holds a letter. -/
def mailboxWorld : Configuration Tm Nat := ⟨[], {0}⟩

def mailboxSpace : Nat → Tm := fun o => if o = 0 then .nm 7 else .nm 3

/-- Everything the mailbox holder writes: its mailbox name, a variable and a letter. -/
def holderTerms : Set Tm := {.nm 3, .var 0, .sym "letter"}

theorem mailboxWorld_wellLocated : WellLocated spaces mailboxSpace mailboxWorld := by
  intro o present
  simp only [mailboxWorld, Finset.mem_singleton] at present
  subst present
  exact ⟨7, resolvesTo_name _ 7⟩

theorem holder_has_no_name_for_store : NoNameFor names mailboxWorld.equations holderTerms 7 := by
  refine ⟨8, by decide, indistinguishable_of_invariant ?_ ?_⟩
  · intro t member
    simp only [holderTerms, Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · simp [mailboxWorld]

/-- **The holder of `m` alone cannot take or read at `n`**: any located step of a rule whose
spaces the holder writes leaves the owner's letter in place. -/
theorem mailbox_holder_cannot_take_at_owner_store {payload : Nat → Tm} {r : LocatedRule Tm}
    {after : Configuration Tm Nat} (known : ∀ s ∈ r.spaces, s ∈ holderTerms)
    (step : LocatedStep spaces mailboxSpace payload r mailboxWorld after) : 0 ∈ after.present :=
  (no_name_no_effect step mailboxWorld_wellLocated known holder_has_no_name_for_store).2.1 0
    (by simp [mailboxWorld]) (resolvesTo_name _ 7)

/-! ### Read-before-take -/

/-- Labels: 0 the owner's row at 7; 1 the ask at 3; 2 the reply at 3; 3 the asker's output at 4. -/
def askLabel : Nat → Tm
  | 0 => .loc (.nm 7) (.sym "v")
  | 1 => .loc (.nm 3) (.sym "ask")
  | 2 => .loc (.nm 3) (.sym "reply")
  | 3 => .loc (.nm 4) (.sym "done")
  | _ => .sym "none"

def rowWorld : Configuration Tm Nat := ⟨[], {0}⟩

/-- The owner takes its row. -/
def ownerTake : LocatedRule Tm := ⟨[(.nm 7, .sym "v")], [], [], [], []⟩

def takeRow : Selection Nat := ⟨[0], [], []⟩

def peekRow : LocatedRule Tm := peekRule (.nm 7) (.sym "v") (.nm 4) (.sym "done")

/-- After the owner took the row. -/
def rowTaken : Configuration Tm Nat := takeRow.result askLabel (ownerTake.toRule spaces) rowWorld

theorem takeRow_valid : takeRow.Valid action askLabel (ownerTake.toRule spaces) rowWorld := by
  refine ⟨by simp [takeRow], by simp [takeRow], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, takeRow, rowWorld], by simp [Selection.commit, takeRow],
      by simp [Selection.commit, takeRow], by simp [Selection.commit, takeRow],
      by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩, by simp [ownerTake, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, ownerTake,
    LocatedRule.toRule, takeRow, rowWorld, place, spaces, askLabel, Tm.subst]

/-- **A primitive read cannot follow the owner's take of its only row.** -/
theorem peek_impossible_after_owner_take (selection : Selection Nat) :
    ¬ selection.Valid action askLabel (peekRow.toRule spaces) rowTaken := by
  intro valid
  have lengths := valid.read_length
  simp only [peekRow, peekRule, LocatedRule.toRule, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil] at lengths
  obtain ⟨x, member⟩ : ∃ x, x ∈ selection.read := by
    cases h : selection.read with
    | nil => rw [h] at lengths; simp at lengths
    | cons x _ => exact ⟨x, by simp⟩
  have present := valid.occurrences.kept_subset (by simpa [Selection.commit] using member)
  simp [rowTaken, Selection.result, fire, Selection.commit, takeRow, rowWorld] at present

def askRow : LocatedRule Tm := sendRule (.nm 3) (.sym "ask")
def serveRow : LocatedRule Tm := serveRule (.nm 3) (.sym "ask") (.nm 7) (.sym "v") (.sym "reply")
def collectRow : LocatedRule Tm := collectRule (.nm 3) (.sym "reply") (.nm 4) (.sym "done")

def asked : Configuration Tm Nat := (makeOne 1).result askLabel (askRow.toRule spaces) rowWorld
def served : Configuration Tm Nat :=
  (serveSel 1 0 2).result askLabel (serveRow.toRule spaces) asked
def servedThenTaken : Configuration Tm Nat :=
  takeRow.result askLabel (ownerTake.toRule spaces) served

/-- **The asker acts after the owner took the row it read**: ask, serve, the owner's take and
the collection all run, in that order. -/
theorem ask_acts_after_owner_take :
    (makeOne 1).Valid action askLabel (askRow.toRule spaces) rowWorld ∧
      (serveSel 1 0 2).Valid action askLabel (serveRow.toRule spaces) asked ∧
      takeRow.Valid action askLabel (ownerTake.toRule spaces) served ∧
      (moveOne 2 3).Valid action askLabel (collectRow.toRule spaces) servedThenTaken ∧
      0 ∉ servedThenTaken.present := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (send_valid_iff (show askLabel 1 = spaces.atSpace (.nm 3) (.sym "ask") from rfl) rowWorld).mpr ⟨⟨Tm.var, by simp [rowWorld]⟩, by simp [rowWorld]⟩
  · refine ⟨by simp [serveSel], by simp [serveSel], rfl, rfl, rfl,
      ⟨?_, ?_, ?_, ?_, by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩,
      by simp [serveRow, serveRule, LocatedRule.toRule]⟩
    · simp [Selection.commit, serveSel, asked, Selection.result, fire, makeOne, rowWorld]
    · simp [Selection.commit, serveSel, asked, Selection.result, fire, makeOne, rowWorld]
    · simp [Selection.commit, serveSel]
    · simp [Selection.commit, serveSel, asked, Selection.result, fire, makeOne, rowWorld]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, serveRow,
        serveRule, askRow, sendRule, LocatedRule.toRule, serveSel, makeOne, asked,
        Selection.result, rowWorld, place, spaces, askLabel, Tm.subst]
  · refine ⟨by simp [takeRow], by simp [takeRow], rfl, rfl, rfl,
      ⟨?_, by simp [Selection.commit, takeRow], by simp [Selection.commit, takeRow],
        by simp [Selection.commit, takeRow], by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩,
      by simp [ownerTake, LocatedRule.toRule]⟩
    · simp [Selection.commit, takeRow, served, asked, Selection.result, fire, makeOne, serveSel,
        rowWorld]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, ownerTake,
        serveRow, serveRule, askRow, sendRule, LocatedRule.toRule, takeRow, serveSel, makeOne,
        served, asked, Selection.result, rowWorld, place, spaces, askLabel, Tm.subst]
  · refine ⟨by simp [moveOne], by simp [moveOne], rfl, rfl, rfl,
      ⟨?_, by simp [Selection.commit, moveOne], by simp [Selection.commit, moveOne], ?_,
        by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩, by simp [collectRow, collectRule,
          LocatedRule.toRule]⟩
    · simp [Selection.commit, moveOne, servedThenTaken, served, asked, Selection.result, fire,
        makeOne, serveSel, takeRow, rowWorld]
    · simp [Selection.commit, moveOne, servedThenTaken, served, asked, Selection.result, fire,
        makeOne, serveSel, takeRow, rowWorld]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, ownerTake,
        collectRow, collectRule, serveRow, serveRule, askRow, sendRule, LocatedRule.toRule,
        takeRow, serveSel, makeOne, moveOne, servedThenTaken, served, asked, Selection.result,
        rowWorld, place, spaces, askLabel, Tm.subst]
  · simp [servedThenTaken, served, asked, Selection.result, fire, Selection.commit, takeRow,
      serveSel, makeOne, rowWorld]

/-! ### Absence -/

/-- Labels: 0 a row `p` the owner makes at 7; 1 the ask; 2 the reply; 3 the asker's output. -/
def absLabel : Nat → Tm
  | 0 => .loc (.nm 7) (.sym "p")
  | 1 => .loc (.nm 3) (.sym "ask")
  | 2 => .loc (.nm 3) (.sym "reply")
  | 3 => .loc (.nm 4) (.sym "done")
  | _ => .sym "none"

def emptyWorld : Configuration Tm Nat := ⟨[], ∅⟩

/-- The primitive guarded act: if no `p` at 7, make `done` at 4. -/
def guardedAct : LocatedRule Tm :=
  ⟨[], [], [], [.absent (.nm 7) (.sym "p")], [(.nm 4, .sym "done")]⟩

/-- The server answers an absence ask from a snapshot. -/
def serveAbsent : LocatedRule Tm :=
  ⟨[(.nm 3, .sym "ask")], [], [], [.absent (.nm 7) (.sym "p")], [(.nm 3, .sym "reply")]⟩

def ownerMake : LocatedRule Tm := sendRule (.nm 7) (.sym "p")

def pPresent : Configuration Tm Nat := (makeOne 0).result absLabel (ownerMake.toRule spaces) emptyWorld

/-- **The primitive absence check refuses to act once `p` is present.** -/
theorem guarded_act_refused_when_present (selection : Selection Nat) :
    ¬ selection.Valid action absLabel (guardedAct.toRule spaces) pPresent := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  have holds := valid.checks (.absent (spaces.atSpace (.nm 7) (.sym "p")))
    (by simp [guardedAct, LocatedRule.toRule, LocatedCheck.toCheck]) σ solved
  have zero : 0 ∈ pPresent.present := by
    simp [pPresent, Selection.result, fire, Selection.commit, makeOne, emptyWorld]
  exact holds 0 zero (by simp [spaces, absLabel, Tm.subst])

def askedAbs : Configuration Tm Nat := (makeOne 1).result absLabel (askRow.toRule spaces) emptyWorld
def servedAbs : Configuration Tm Nat :=
  (moveOne 1 2).result absLabel (serveAbsent.toRule spaces) askedAbs
def madeAfterServe : Configuration Tm Nat :=
  (makeOne 0).result absLabel (ownerMake.toRule spaces) servedAbs

/-- **The asker acts on the server's earlier answer while `p` is present.** -/
theorem ask_absence_acts_when_present :
    (makeOne 1).Valid action absLabel (askRow.toRule spaces) emptyWorld ∧
      (moveOne 1 2).Valid action absLabel (serveAbsent.toRule spaces) askedAbs ∧
      (makeOne 0).Valid action absLabel (ownerMake.toRule spaces) servedAbs ∧
      (moveOne 2 3).Valid action absLabel (collectRow.toRule spaces) madeAfterServe ∧
      0 ∈ madeAfterServe.present := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (send_valid_iff (show absLabel 1 = spaces.atSpace (.nm 3) (.sym "ask") from rfl) emptyWorld).mpr ⟨⟨Tm.var, by simp [emptyWorld]⟩, by simp [emptyWorld]⟩
  · refine ⟨by simp [moveOne], by simp [moveOne], rfl, rfl, rfl,
      ⟨?_, by simp [Selection.commit, moveOne], by simp [Selection.commit, moveOne], ?_,
        by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩, ?_⟩
    · simp [Selection.commit, moveOne, askedAbs, Selection.result, fire, makeOne, emptyWorld]
    · simp [Selection.commit, moveOne, askedAbs, Selection.result, fire, makeOne, emptyWorld]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, serveAbsent,
        askRow, sendRule, LocatedRule.toRule, moveOne, makeOne, askedAbs, Selection.result,
        emptyWorld, place, spaces, absLabel, Tm.subst]
    · intro check member σ _
      simp only [serveAbsent, LocatedRule.toRule, LocatedCheck.toCheck, List.map_cons,
        List.map_nil, List.mem_singleton] at member
      subst member
      intro o present
      simp [askedAbs, Selection.result, fire, Selection.commit, makeOne, emptyWorld] at present
      subst present
      simp [spaces, absLabel, Tm.subst]
  · refine (send_valid_iff (show absLabel 0 = spaces.atSpace (.nm 7) (.sym "p") from rfl) servedAbs).mpr ⟨⟨Tm.var, ?_⟩, ?_⟩
    · simp [SubstitutionAction.Solves, servedAbs, askedAbs, Selection.result, Selection.problem,
        Selection.equations, serveAbsent, askRow, sendRule, LocatedRule.toRule, moveOne, makeOne,
        emptyWorld, place, spaces, absLabel, Tm.subst]
    · simp [servedAbs, askedAbs, Selection.result, fire, Selection.commit, moveOne, makeOne,
        emptyWorld]
  · refine ⟨by simp [moveOne], by simp [moveOne], rfl, rfl, rfl,
      ⟨?_, by simp [Selection.commit, moveOne], by simp [Selection.commit, moveOne], ?_,
        by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩, by simp [collectRow, collectRule,
          LocatedRule.toRule]⟩
    · simp [Selection.commit, moveOne, madeAfterServe, servedAbs, askedAbs, Selection.result,
        fire, makeOne, emptyWorld]
    · simp [Selection.commit, moveOne, madeAfterServe, servedAbs, askedAbs, Selection.result,
        fire, makeOne, emptyWorld]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, madeAfterServe,
        servedAbs, askedAbs, Selection.result, collectRow, collectRule, ownerMake, serveAbsent,
        askRow, sendRule, LocatedRule.toRule, moveOne, makeOne, emptyWorld, place, spaces,
        absLabel, Tm.subst]
  · simp [madeAfterServe, Selection.result, fire, Selection.commit, makeOne]

/-! ### Copies -/

/-- Labels: 0 the owner's one row; 1 and 5 asks; 2 and 6 replies. -/
def copyLabel : Nat → Tm
  | 0 => .loc (.nm 7) (.sym "v")
  | 1 => .loc (.nm 3) (.sym "ask")
  | 2 => .loc (.nm 3) (.sym "reply")
  | 5 => .loc (.nm 3) (.sym "ask")
  | 6 => .loc (.nm 3) (.sym "reply")
  | _ => .sym "none"

def askedTwice : Configuration Tm Nat :=
  (makeOne 5).result copyLabel (askRow.toRule spaces)
    ((makeOne 1).result copyLabel (askRow.toRule spaces) rowWorld)

def servedTwice : Configuration Tm Nat :=
  (serveSel 5 0 6).result copyLabel (serveRow.toRule spaces)
    ((serveSel 1 0 2).result copyLabel (serveRow.toRule spaces) askedTwice)

theorem servedTwice_present : servedTwice.present = {0, 2, 6} := by
  ext x
  simp only [servedTwice, askedTwice, Selection.result, fire, Selection.commit, serveSel,
    makeOne, rowWorld, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert, Finset.sdiff_empty]
  omega

/-- **Two asks served from one row leave two reply occurrences**, while the owner's space still
holds its one row: the answers are copies with identities of their own. -/
theorem two_asks_two_copies :
    (serveSel 1 0 2).Valid action copyLabel (serveRow.toRule spaces) askedTwice ∧
      (serveSel 5 0 6).Valid action copyLabel (serveRow.toRule spaces)
        ((serveSel 1 0 2).result copyLabel (serveRow.toRule spaces) askedTwice) ∧
      2 ∈ servedTwice.present ∧ 6 ∈ servedTwice.present ∧ 2 ≠ 6 ∧
      copyLabel 2 = copyLabel 6 ∧
      (∀ o ∈ servedTwice.present, copyLabel o = .loc (.nm 7) (.sym "v") → o = 0) := by
  have askedPresent : askedTwice.present = {0, 1, 5} := by
    ext x
    simp only [askedTwice, Selection.result, fire, Selection.commit, makeOne, rowWorld,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_insert, Finset.sdiff_empty]
    omega
  have askedEquations : askedTwice.equations = [] := by
    simp [askedTwice, Selection.result, Selection.problem, Selection.equations, makeOne,
      askRow, sendRule, LocatedRule.toRule, rowWorld]
  refine ⟨?_, ?_, by simp [servedTwice_present], by simp [servedTwice_present], by decide, rfl, ?_⟩
  · refine ⟨by simp [serveSel], by simp [serveSel], rfl, rfl, rfl,
      ⟨?_, ?_, by simp [Selection.commit, serveSel], ?_, by simp [Selection.commit]⟩,
      ⟨Tm.var, ?_⟩, by simp [serveRow, serveRule, LocatedRule.toRule]⟩
    · simp [Selection.commit, serveSel, askedPresent]
    · simp [Selection.commit, serveSel, askedPresent]
    · simp [Selection.commit, serveSel, askedPresent]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, serveRow,
        serveRule, LocatedRule.toRule, serveSel, askedEquations, place, spaces, copyLabel,
        Tm.subst]
  · refine ⟨by simp [serveSel], by simp [serveSel], rfl, rfl, rfl,
      ⟨?_, ?_, by simp [Selection.commit, serveSel], ?_, by simp [Selection.commit]⟩,
      ⟨Tm.var, ?_⟩, by simp [serveRow, serveRule, LocatedRule.toRule]⟩
    · simp [Selection.commit, serveSel, Selection.result, fire, askedPresent]
    · simp [Selection.commit, serveSel, Selection.result, fire, askedPresent]
    · simp [Selection.commit, serveSel, Selection.result, fire, askedPresent]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, serveRow,
        serveRule, LocatedRule.toRule, serveSel, Selection.result, askedEquations, place,
        spaces, copyLabel, Tm.subst]
  · intro o present labelled
    rw [servedTwice_present] at present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl
    · rfl
    · simp [copyLabel] at labelled
    · simp [copyLabel] at labelled

/-! ### Atomicity: the forwarder is a second firing -/

/-- Labels: 0 the primitive delivery at 7; 1 the post at 3; 2 the signal at 5; 9 an alarm at 6. -/
def gapLabel : Nat → Tm
  | 0 => .loc (.nm 7) (.sym "letter")
  | 1 => .loc (.nm 3) (.sym "letter")
  | 2 => .loc (.nm 5) (.sym "sent")
  | 9 => .loc (.nm 6) (.sym "alarm")
  | _ => .sym "none"

/-- The client posts at its mailbox and signals that it has sent. -/
def postAndSignal : LocatedRule Tm :=
  ⟨[], [], [], [], [(.nm 3, .sym "letter"), (.nm 5, .sym "sent")]⟩

/-- The primitive: send at the owner's store and signal. -/
def sendAndSignal : LocatedRule Tm :=
  ⟨[], [], [], [], [(.nm 7, .sym "letter"), (.nm 5, .sym "sent")]⟩

/-- An observer: having seen the signal, raise an alarm if the letter is not at 7. -/
def alarm : LocatedRule Tm :=
  ⟨[], [(.nm 5, .sym "sent")], [], [.absent (.nm 7) (.sym "letter")], [(.nm 6, .sym "alarm")]⟩

def posted : Configuration Tm Nat :=
  (⟨[], [], [1, 2]⟩ : Selection Nat).result gapLabel (postAndSignal.toRule spaces) emptyWorld

def sent : Configuration Tm Nat :=
  (⟨[], [], [0, 2]⟩ : Selection Nat).result gapLabel (sendAndSignal.toRule spaces) emptyWorld

/-- **The intermediate state is observable**: after the client's post and signal, an observer
ordered after the signal sees the letter missing at the owner's store. -/
theorem forwarder_gap_observable :
    (⟨[], [], [1, 2]⟩ : Selection Nat).Valid action gapLabel (postAndSignal.toRule spaces)
        emptyWorld ∧
      (⟨[], [2], [9]⟩ : Selection Nat).Valid action gapLabel (alarm.toRule spaces) posted := by
  constructor
  · refine ⟨by simp, by simp, rfl, rfl, rfl,
      ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
        by simp [Selection.commit, emptyWorld], by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩,
      by simp [postAndSignal, LocatedRule.toRule]⟩
    simp [Selection.problem, Selection.equations, postAndSignal, LocatedRule.toRule, emptyWorld]
  · refine ⟨by simp, by simp, rfl, rfl, rfl,
      ⟨by simp [Selection.commit], ?_, by simp [Selection.commit], ?_, by simp [Selection.commit]⟩,
      ⟨Tm.var, ?_⟩, ?_⟩
    · simp [Selection.commit, posted, Selection.result, fire, emptyWorld]
    · simp [Selection.commit, posted, Selection.result, fire, emptyWorld]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, alarm,
        postAndSignal, LocatedRule.toRule, posted, Selection.result, emptyWorld, place, spaces,
        gapLabel, Tm.subst]
    · intro check member σ _
      simp only [alarm, LocatedRule.toRule, LocatedCheck.toCheck, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst member
      intro o present
      simp [posted, Selection.result, fire, Selection.commit, emptyWorld] at present
      rcases present with rfl | rfl <;> simp [spaces, gapLabel, Tm.subst]

/-- **After the primitive send no observer sees the gap.** -/
theorem primitive_send_no_gap (selection : Selection Nat) :
    ¬ selection.Valid action gapLabel (alarm.toRule spaces) sent := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  have holds := valid.checks (.absent (spaces.atSpace (.nm 7) (.sym "letter")))
    (by simp [alarm, LocatedRule.toRule, LocatedCheck.toCheck]) σ solved
  have zero : 0 ∈ sent.present := by
    simp [sent, Selection.result, fire, Selection.commit, emptyWorld]
  exact holds 0 zero (by simp [spaces, gapLabel, Tm.subst])

/-! ### Shared forwarder names -/

def mailLabel : Nat → Tm := fun _ => .loc (.nm 3) (.sym "letter")

def mailSpace : Nat → Tm := fun _ => .nm 3

def mailPayload : Nat → Tm := fun _ => .sym "letter"

/-- Client 1's post sits at the shared mailbox 3. -/
def postedWorld : Configuration Tm Nat := ⟨[], {1}⟩

/-- Client 2, holding the same name, takes whatever is posted there. -/
def thief : LocatedRule Tm := ⟨[(.nm 3, .var 0)], [], [], [], []⟩

/-- **Holders of one name have full authority over it**: client 2 takes client 1's post. -/
theorem shared_mailbox_intercepted :
    LocatedStep spaces mailSpace mailPayload thief postedWorld
      ((⟨[1], [], []⟩ : Selection Nat).result (located spaces mailSpace mailPayload)
        (thief.toRule spaces) postedWorld) := by
  refine ⟨?_, ⟨[1], [], []⟩, ?_, rfl⟩
  · intro s member
    simp [LocatedRule.spaces, thief] at member
    subst member
    exact ⟨3, resolvesTo_name _ 3⟩
  · refine ⟨by simp, by simp, rfl, rfl, rfl,
      ⟨by simp [Selection.commit, postedWorld], by simp [Selection.commit],
        by simp [Selection.commit], by simp [Selection.commit, postedWorld],
        by simp [Selection.commit]⟩, ⟨fun _ => .sym "letter", ?_⟩,
      by simp [thief, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, thief,
      LocatedRule.toRule, postedWorld, place, located, spaces, mailSpace, mailPayload, Tm.subst]

/-- Client 2 with its own fresh mailbox 8 writes only these terms. -/
def otherHolderTerms : Set Tm := {.nm 8, .var 0}

theorem postedWorld_wellLocated : WellLocated spaces mailSpace postedWorld :=
  fun _ _ => ⟨3, resolvesTo_name _ 3⟩

/-- **With one fresh name per holder the other holder cannot intercept**: any located step of a
rule whose spaces client 2 writes leaves client 1's post in place. -/
theorem separate_mailbox_not_intercepted {r : LocatedRule Tm} {after : Configuration Tm Nat}
    (known : ∀ s ∈ r.spaces, s ∈ otherHolderTerms)
    (step : LocatedStep spaces mailSpace mailPayload r postedWorld after) : 1 ∈ after.present := by
  have noName : NoNameFor names postedWorld.equations otherHolderTerms 3 := by
    refine ⟨9, by decide, indistinguishable_of_invariant ?_ ?_⟩
    · intro t member
      simp only [otherHolderTerms, Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl <;> rfl
    · simp [postedWorld]
  exact (no_name_no_effect step postedWorld_wellLocated known noName).2.1 1
    (by simp [postedWorld]) (resolvesTo_name _ 3)

/-! ### Reads write bindings -/

/-- The owner's row at 7 holds an open variable 9. -/
def openLabel : Nat → Tm := fun _ => .loc (.nm 7) (.app (.sym "p") (.var 9))

def openWorld : Configuration Tm Nat := ⟨[], {0}⟩

/-- A reader with a ground pattern. -/
def groundPeek : LocatedRule Tm := ⟨[], [(.nm 7, .app (.sym "p") (.sym "a"))], [], [], []⟩

def readOpen : Selection Nat := ⟨[], [0], []⟩

/-- **A read binds the owner's variable**: before the read variable 9 is free; after it, every
solution sends it to `a`. -/
theorem peek_binds_owner_variable :
    readOpen.Valid action openLabel (groundPeek.toRule spaces) openWorld ∧
      (∃ σ, action.Models σ openWorld.equations ∧ σ 9 ≠ .sym "a") ∧
      ∀ σ, action.Models σ
        (readOpen.result openLabel (groundPeek.toRule spaces) openWorld).equations →
          σ 9 = .sym "a" := by
  refine ⟨?_, ⟨Tm.var, by simp [openWorld], by simp⟩, ?_⟩
  · refine ⟨by simp [readOpen], by simp [readOpen], rfl, rfl, rfl,
      ⟨by simp [Selection.commit, readOpen], by simp [Selection.commit, readOpen, openWorld],
        by simp [Selection.commit, readOpen], by simp [Selection.commit, readOpen],
        by simp [Selection.commit]⟩, ⟨fun _ => .sym "a", ?_⟩,
      by simp [groundPeek, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, groundPeek,
      LocatedRule.toRule, readOpen, openWorld, place, spaces, openLabel, Tm.subst]
  · intro σ solved
    simp [SubstitutionAction.Solves, Selection.result, Selection.problem, Selection.equations,
      groundPeek, LocatedRule.toRule, readOpen, openWorld, place, spaces, openLabel,
      Tm.subst] at solved
    exact solved.symm

/-! ### Every observation agrees: a concrete instance -/

/-- Labels: 0 the primitive delivery of a letter at 7; 1 the post at 3; 2 the forwarded
occurrence at 7, whose payload is the forwarder's variable 5. -/
def fwdLabel : Nat → Tm
  | 0 => .loc (.nm 7) (.sym "letter")
  | 1 => .loc (.nm 3) (.sym "letter")
  | 2 => .loc (.nm 7) (.var 5)
  | _ => .sym "none"

/-- The count of letters at the owner's store. -/
def lettersAtSeven : Check Tm := .count (.loc (.nm 7) (.sym "letter")) 1

/-- **Positive control**: after the post and the forwarding, every solution counts exactly one
letter at 7, as after the primitive send; the theorem transfers the verdict. -/
theorem forwarded_count_entailed :
    action.Entails
      (forwardedAt spaces fwdLabel (.nm 3) (.nm 7) (.sym "letter") (.var 5) 1 2 emptyWorld).equations
      (fun σ => lettersAtSeven.Holds action σ fwdLabel
        (forwardedAt spaces fwdLabel (.nm 3) (.nm 7) (.sym "letter") (.var 5) 1 2
          emptyWorld).present) := by
  have transfer := forwarder_observations_agree (sts := spaces) (label := fwdLabel) (m := 3)
    (n := 7) (q := .sym "letter") (X := .var 5) (o := 0) (o1 := 1) (o2 := 2) rfl rfl rfl
    (C := emptyWorld) (by simp [emptyWorld]) (by simp [emptyWorld]) (by simp [emptyWorld])
    (by decide) ⟨fun _ => .sym "letter", by simp [emptyWorld, SubstitutionAction.Solves,
      Tm.subst]⟩ lettersAtSeven ?_
  · apply transfer.mpr
    intro σ _
    classical
    show (Check.matches action σ fwdLabel _ _).card = 1
    rw [sentAt_present]
    simp [Check.matches, emptyWorld, Finset.filter_singleton, fwdLabel, Tm.subst]
  · intro σ _
    refine ⟨fun i => if i = 5 then .sym "letter" else σ i, ?_, ?_, ?_⟩
    · simp [emptyWorld, SubstitutionAction.Solves, Tm.subst]
    · intro t member
      simp only [checkTerms, lettersAtSeven, List.mem_singleton] at member
      subst member
      simp [Tm.subst]
    · intro x member
      simp only [emptyWorld, Finset.mem_insert, Finset.notMem_empty, or_false] at member
      subst member
      simp [fwdLabel, Tm.subst]

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces
