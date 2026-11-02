import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Calculus
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedSteps

/-!
# The guarded rewriting calculus on thinned shared terms

The assembled calculus (`GuardedMultisetRewriting.Calculus`) is generic in its term layer: terms, patterns
with variables, and a declared theory `E`. This module gives it its term layer: **binding trees,
stored as co-de-Bruijn DAGs with thinnings on edges**.

**Terms.** `treeCalculus space` is the calculus whose terms are binding trees
(`SignatureIndexedABT.Term`), compared as nameless trees, so up to alpha-equivalence. A
`Proc`/value reader and an `Atom`/syntax reader see binding trees alike: on trees the declared
theory is equality, so value and syntax equality coincide (`treeCalculus_layer`). (The contract
words follow Zar's decision of 2026-10-29: `Atom` is data, read as syntax and not evaluated;
`Proc` is computation, read as its value. The constructors of `Contract` are still named
`.data` and `.value`.) The reflection results of `GuardedMultisetRewriting.Reflection` hold for every term
layer, so they hold here; they say something new only where a value theory is coarser than syntax,
as for bags.

**Configurations on the store.** A configuration is a canonical thinned store and a bag of
canonical references; it stands for the bag of trees the references unfold to (`trees`).

**Results.**

* A process's shared step is a step of the process on the trees, and every step of the process on
  the trees is a shared step (`sharedProcessStep_sound`, `sharedProcessStep_complete`), built on
  `sharedStep_sound` and `sharedStep_complete`.
* **LCF on shared configurations**: a process without `send` at a space never adds a term there,
  whichever store it runs on (`sharedProcessStep_no_make_without_send`).
* **Need cells are shared nodes**: keying each demand by its term's reference shares exactly the
  demands for alpha-equivalent terms (`nodeSharing_sound`, `nodeSharing_complete`). Keying by the
  node alone shares the demands whose terms differ by a renaming of their free variables
  (`nodeIdSharing_sound`, `nodeIdSharing_complete`); this is the context-free sharing of the
  thinned store, sound for any meaning that is a function of the term's code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uN

variable {Head : Type} {V : Type} {N : Type uN}

section TreeCalculus

variable [DecidableEq V]

/-- **The binding-tree calculus**: terms are binding trees compared up to alpha-equivalence, a
`Proc`/value reader and an `Atom`/syntax reader alike, each term in its space. -/
def treeCalculus (space : SignatureIndexedABT.Term Head → N) :
    Calculus V (SignatureIndexedABT.Term Head) (TreePat Head V) N where
  asValues := treeLayer
  asSyntax := treeLayer
  finer := fun _ _ h => h
  space := space

/-- Both readings of the contract are the binding-tree term layer. -/
theorem treeCalculus_layer (space : SignatureIndexedABT.Term Head → N) (contract : Contract) :
    (treeCalculus (V := V) space).readers.layer contract = treeLayer := by
  cases contract <;> rfl

end TreeCalculus

variable [DecidableEq V] [DecidableEq Head] {space : SignatureIndexedABT.Term Head → N}

/-! ## Processes on the thinned store -/

/-- **A shared step of a process**: one of its rules steps on references. -/
def SharedProcessStep (proc : (treeCalculus (V := V) space).Process) (St : Store Head)
    (bag : Multiset Ref) (St' : Store Head) (bag' : Multiset Ref) : Prop :=
  ∃ cr ∈ proc.rules, SharedStep cr.2 St bag St' bag'

/-- **Every shared step of a process is a step of the process on the trees**, and the store only
grows and stays canonical. -/
theorem sharedProcessStep_sound {proc : (treeCalculus (V := V) space).Process}
    {St St' : Store Head} {bag bag' : Multiset Ref} (canon : Canonical St)
    (hbag : ∀ x ∈ bag, CanonRef St x) (step : SharedProcessStep proc St bag St' bag') :
    St <+: St' ∧ Canonical St' ∧ (∀ x ∈ bag', CanonRef St' x) ∧
      proc.Step (trees St bag) (trees St' bag') := by
  obtain ⟨cr, mem, shared⟩ := step
  obtain ⟨grow, canon', hbag', tree⟩ := sharedStep_sound canon hbag shared
  refine ⟨grow, canon', hbag', cr, mem, ?_⟩
  rw [treeCalculus_layer]
  exact tree

/-- **Every step of a process on the trees is the unfolding of a shared step.** -/
theorem sharedProcessStep_complete {proc : (treeCalculus (V := V) space).Process}
    {St : Store Head} {bag : Multiset Ref} (canon : Canonical St) (hbag : ∀ x ∈ bag, CanonRef St x)
    {M' : Multiset (SignatureIndexedABT.Term Head)} (step : proc.Step (trees St bag) M') :
    ∃ St' bag', SharedProcessStep proc St bag St' bag' ∧ trees St' bag' = M' := by
  obtain ⟨cr, mem, tree⟩ := step
  rw [treeCalculus_layer] at tree
  obtain ⟨St', bag', shared, eq⟩ := sharedStep_complete canon hbag tree
  exact ⟨St', bag', ⟨cr, mem, shared⟩, eq⟩

/-- **LCF on shared configurations**: a process that does not hold `send` at a space adds no term
there. With the theorem space writable only by the kernel, only kernel steps make theorems,
whichever store the terms live in. -/
theorem sharedProcessStep_no_make_without_send [DecidableEq N]
    {proc : (treeCalculus (V := V) space).Process} {St St' : Store Head} {bag bag' : Multiset Ref}
    (canon : Canonical St) (hbag : ∀ x ∈ bag, CanonRef St x)
    (step : SharedProcessStep proc St bag St' bag') {n : N} (noSend : proc.rights n .send = false) :
    snapshot space n (trees St' bag') ≤ snapshot space n (trees St bag) :=
  Calculus.Process.Step.no_make_without_send (sharedProcessStep_sound canon hbag step).2.2.2 noSend

/-! ## Need cells are shared nodes -/

section NeedSharing

open Mettapedia.GSLT.Dynamics.ProofRelevantNeed

variable {Site : Type*}

/-- **Need cells keyed by references**: each demand site holds a reference to its term; demands
with the same reference share one cell. -/
def nodeSharing (term : Site → Ref) : SharingScheme Site := ⟨Ref, inferInstance, term⟩

omit [DecidableEq V] [DecidableEq Head] in
/-- Sharing by reference is sound: demands that share a cell demand the same term. -/
theorem nodeSharing_sound (St : Store Head) (term : Site → Ref) :
    (nodeSharing term).SoundFor (fun s => unfold St (term s)) := by
  intro left right shares
  change term left = term right at shares
  simp only [shares]

omit [DecidableEq V] [DecidableEq Head] in
/-- **Sharing by reference is complete**: in a canonical store, demands for equal
(alpha-equivalent) terms share one cell. -/
theorem nodeSharing_complete {St : Store Head} (canon : Canonical St) {term : Site → Ref}
    (canonical : ∀ s, CanonRef St (term s)) {left right : Site}
    (same : unfold St (term left) = unfold St (term right)) : (nodeSharing term).Shares left right :=
  (unfold_eq_iff canon (canonical left) (canonical right)).mp same

/-- **Need cells keyed by nodes**: demands whose references point to one node share a cell. -/
def nodeIdSharing (term : Site → Ref) : SharingScheme Site := ⟨ℕ, inferInstance, fun s => (term s).id⟩

omit [DecidableEq V] [DecidableEq Head] in
/-- Sharing by node is sound for every meaning that depends only on a term's code: demands that
share a cell demand terms with one code. -/
theorem nodeIdSharing_sound {St : Store Head} (canon : Canonical St) {term : Site → Ref}
    (canonical : ∀ s, CanonRef St (term s)) :
    (nodeIdSharing term).SoundFor (fun s => (encode (unfold St (term s))).2) := by
  intro left right shares
  exact (same_node_iff canon (Or.inl (canonical left)) (Or.inl (canonical right))).mp shares

omit [DecidableEq V] [DecidableEq Head] in
/-- **Sharing by node is complete up to renaming**: demands for terms that differ by a thinning of
their free variables share one cell. -/
theorem nodeIdSharing_complete {St : Store Head} (canon : Canonical St) {term : Site → Ref}
    (canonical : ∀ s, CanonRef St (term s)) {left right : Site} {ρ : Thin}
    (renamed : unfold St (term right) = rename ρ (unfold St (term left))) :
    (nodeIdSharing term).Shares left right :=
  (renamed_one_node canon (Or.inl (canonical left)) (Or.inl (canonical right)) renamed).symm

end NeedSharing

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
