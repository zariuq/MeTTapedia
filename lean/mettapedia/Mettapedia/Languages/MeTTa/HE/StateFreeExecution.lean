/-
# Derivation-local state-free execution

The environment-level predicate `MinEnvStateOpFree` asks that EVERY atom the
static environment can produce is state-operation-free.  That is too strong to
be the seal's boundary, and provably so: the shipped prelude declares
`(: add-atom (-> SpaceType Atom (->)))` and defines
`(= (add-reduct $dst $atom) (add-atom $dst $atom))`, so any environment
carrying those declarations fails it outright
(`not_strictGlobalProfile_of_declares_addAtom` below).  Yet most executions in
that prelude never reach a mutation — the mutation-capable rules are simply
never selected.

So the boundary belongs to the DERIVATION, not to the environment.  A
`StateFreeExecution` certificate is an invariant on the configurations a run
actually reaches: it must be preserved by each step and must forbid world
mutation at each reached step.  Nothing is asked about configurations the run
never visits.

Two design points, both forced by the runtime:

* **The invariant is indexed by `World`, not by `St`.**  A step may advance the
  gensym counter (`St.fresh`) while leaving the world alone, and the world is
  exactly what the certificate protects.  Indexing by `World` is what lets the
  SIBLING work items stay certified across a step: after the step the world is
  unchanged, so their invariant still holds verbatim.  Indexing by `St` would
  force an extra stability obligation for no gain.

* **`St.mapWorld` is the unique world funnel.**  `St` has two fields, and the
  only expressions building or updating one are `St.init`, `St.fresh` (counter
  only), `St.mapWorld`, and three counter-only record updates.  So world change
  in `interpretFuel` can enter only through `interpretStack1`, which is why the
  lifting theorem below needs a hypothesis about single steps and nothing else.

Global environment closure is retained as `StrictGlobalProfile`: a sufficient,
derivation-independent condition, kept because it is checkable without
reference to a particular run.  It is strictly stronger — the full prelude
refutes it while still allowing certified pure runs.
-/
import Mettapedia.Languages.MeTTa.HE.StateFreeFragment
import MettaHyperonFull.Minimal.Stdlib
import MettaHyperonFull.Proofs.Substitution

namespace Mettapedia.Languages.MeTTa.HE.StateFreeExecution

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE.StateFreeFragment

/-! ## The certificate -/

/-- A derivation-local state-free execution certificate for `env`.

`Inv w it` marks the configurations the run is allowed to reach.  The two
obligations are exactly what the lifting theorem consumes: a reached
configuration must not mutate the world, and its successors must again be
reached configurations.  Configurations outside `Inv` are unconstrained. -/
structure Certificate (env : MinEnv) (Inv : World → Item → Prop) : Prop where
  /-- No reached step mutates the world. -/
  preserves : ∀ (fuel : Nat) (st : St) (it : Item), Inv st.world it →
    (interpretStack1 env fuel st it).2.world = st.world
  /-- Successors of a reached configuration are reached. -/
  reached : ∀ (fuel : Nat) (st : St) (it : Item), Inv st.world it →
    ∀ it' ∈ (interpretStack1 env fuel st it).1, Inv st.world it'

/-! ## Single steps

Real, unconditional content: the finished-frame arms of `interpretStack1`
return the incoming state untouched, so they preserve the world with no
hypothesis about the environment at all. -/

/-- An exhausted stack is inert. -/
theorem interpretStack1_preservesWorld_of_nil (env : MinEnv) (fuel : Nat)
    (st : St) (it : Item) (hstack : it.stack = []) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp [interpretStack1, hstack]

/-- Every return arm of a FINISHED frame threads the incoming state unchanged,
so the world survives regardless of `env`, the bindings, or the frame's
continuation. -/
theorem interpretStack1_preservesWorld_of_fin (env : MinEnv) (fuel : Nat)
    (st : St) (it : Item) (top : Frame) (prev : Stack)
    (hstack : it.stack = top :: prev) (hfin : top.fin = true) :
    (interpretStack1 env fuel st it).2.world = st.world := by
  simp only [interpretStack1, hstack, hfin, if_true]
  -- every finished-frame arm returns the incoming state, so the split tree
  -- closes uniformly by reflexivity
  repeat' split
  all_goals rfl

/-! ## Lifting one step to a whole run

The theorem the seal needs.  Induction on the fuel budget; the world is
carried through the recursion by the certificate, and the sibling work items
remain certified precisely because the invariant is world-indexed. -/

/-- **`interpretFuel` preserves the world on a certified run.** -/
theorem interpretFuel_preservesWorld {env : MinEnv} {Inv : World → Item → Prop}
    (cert : Certificate env Inv) :
    ∀ (fuel : Nat) (st : St) (work : List Item) (done : List (Atom × Bindings)),
      (∀ it ∈ work, Inv st.world it) →
      (interpretFuel env fuel st work done).2.world = st.world := by
  intro fuel
  induction fuel with
  | zero =>
      intro st work done _
      cases work with
      | nil => simp [interpretFuel]
      | cons it rest => simp [interpretFuel]
  | succ fuel ih =>
      intro st work done hwork
      cases work with
      | nil => simp [interpretFuel]
      | cons it rest =>
          have hit : Inv st.world it := hwork it (by simp)
          have hstep : (interpretStack1 env fuel st it).2.world = st.world :=
            cert.preserves fuel st it hit
          simp only [interpretFuel]
          rw [ih (interpretStack1 env fuel st it).2 _ _ ?_, hstep]
          intro it' member
          rw [hstep]
          rcases List.mem_append.mp member with h | h
          · exact cert.reached fuel st it hit it' (List.mem_filter.mp h).1
          · exact hwork it' (by simp [h])

/-! ## The strict global profile

Retained, but demoted: a sufficient condition that does not mention any
derivation.  It is genuinely stronger than a certificate, as the prelude
witness below shows. -/

/-- Environment-level closure: every producer interface is state-operation-free.
This is derivation-INDEPENDENT, hence checkable once per environment — its
only advantage over a certificate, and the reason to keep it. -/
structure StrictGlobalProfile (env : MinEnv) : Prop where
  environment : MinEnvStateOpFree env
  grounded : GroundingTableStateOpFree env.gt

/-! ## Witnesses

A boundary is only meaningful if it both ACCEPTS real runs and REJECTS real
mutations.  Both are exhibited in the shipped prelude environment, not in a
toy environment built to make the statement true. -/

/-- The genuine prelude environment, exactly as the runners build it. -/
def fullPreludeEnv : MinEnv :=
  { MinEnv.ofAtomsGT (preludeAtoms ++ []) stdGroundings with visibleAtoms := [] }

/-- A pending inert-symbol item, used only to witness the syntactic side of
the fragment boundary. -/
def pendingPureItem : Item :=
  { stack := [{ atom := Atom.sym "a", fin := false }], bnd := [] }

/-- A mutating item: `(add-atom &self A)`, the shape the fragment must reject. -/
def mutatingItem : Item :=
  { stack := [{ atom := Atom.expr [Atom.sym "add-atom", Atom.sym "&self",
      Atom.sym "A"], fin := false }], bnd := [] }

/-- POSITIVE: the pure item is in the syntactic fragment. -/
theorem pendingPureItem_atom_stateOpFree : StateOpFree (Atom.sym "a") := by
  simp [StateOpFree, worldMutatingHeads]

/-- NEGATIVE: the mutating item is not, so the two witnesses are genuinely on
opposite sides of the boundary. -/
theorem mutatingItem_not_stateOpFree :
    ¬ StateOpFree (Atom.expr [Atom.sym "add-atom", Atom.sym "&self",
      Atom.sym "A"]) := by
  rintro ⟨head, -⟩
  exact absurd (head "add-atom" [Atom.sym "&self", Atom.sym "A"] rfl) (by decide)

/-! ### A certified pure execution in the full prelude

The invariant below is discharged WITHOUT reducing the prelude, which matters:
`preludeAtoms` is produced by running the parser over a 152-atom source, and
kernel reduction of that parse is not viable.  The finished-frame class needs
no environment lookup at all, so the certificate holds for EVERY environment —
and therefore for the genuine prelude environment, mutation-capable rules and
all.  That is exactly the point being made: a run is certified by what it
reaches, not by what its environment could have offered. -/

/-- Reached configurations of a returning run: a single finished frame. -/
def FinishedInv (_ : World) (it : Item) : Prop :=
  ∃ top : Frame, it.stack = [top] ∧ top.fin = true

/-- **The certificate, for an arbitrary environment.**  Both obligations hold
structurally: a lone finished frame returns itself and never touches the
world. -/
theorem finished_stateFreeExecution (env : MinEnv) :
    Certificate env FinishedInv where
  preserves := by
    rintro fuel st it ⟨top, hstack, hfin⟩
    exact interpretStack1_preservesWorld_of_fin env fuel st it top [] hstack hfin
  reached := by
    rintro fuel st it ⟨top, hstack, hfin⟩ it' member
    simp only [interpretStack1, hstack, hfin, if_true] at member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨top, hstack, hfin⟩

/-- **A pure execution in the full prelude preserves the world**, at any fuel
budget and for any accumulated results. -/
theorem fullPrelude_pure_run_preservesWorld
    (fuel : Nat) (st : St) (work : List Item)
    (done : List (Atom × Bindings))
    (hwork : ∀ it ∈ work, FinishedInv st.world it) :
    (interpretFuel fullPreludeEnv fuel st work done).2.world = st.world :=
  interpretFuel_preservesWorld (finished_stateFreeExecution fullPreludeEnv)
    fuel st work done hwork

/-- The pure witness is in the certified class, so the theorem above is not
vacuous on it. -/
theorem pureFinished_inv (w : World) :
    FinishedInv w { stack := [{ atom := Atom.sym "a", fin := true }], bnd := [] } :=
  ⟨{ atom := Atom.sym "a", fin := true }, rfl, rfl⟩

/-- Concretely: harvesting a finished inert-symbol item in the genuine prelude
environment leaves the world untouched.  This is the scheduler base case, not
a certificate for a pending evaluation. -/
theorem fullPrelude_finishedItem_preservesWorld (fuel : Nat) :
    (interpretFuel fullPreludeEnv fuel St.init
      [{ stack := [{ atom := Atom.sym "a", fin := true }], bnd := [] }] []).2.world
      = St.init.world := by
  refine fullPrelude_pure_run_preservesWorld fuel St.init _ [] ?_
  intro it member
  rcases List.mem_singleton.mp member with rfl
  exact pureFinished_inv _

/-! ### A rejected mutation execution

The mutating item is NOT in the certified class, and not merely by omission:
stepping it actually writes the world, so no certificate whatsoever can cover
it.  This is what stops the boundary from being satisfiable by fiat. -/

/-- The mutating item is outside the certified class. -/
theorem mutatingItem_not_finishedInv (w : World) : ¬ FinishedInv w mutatingItem := by
  rintro ⟨top, hstack, hfin⟩
  simp only [mutatingItem] at hstack
  cases hstack
  simp at hfin

/-- **The mutation really writes the world.**  Stepping the mutating item in
the genuine prelude environment appends to `&self`, so the step is not
world-preserving.  Rejection is therefore forced, not a matter of the
invariant happening to omit it. -/
theorem mutatingItem_step_writes_world (fuel : Nat) :
    (interpretStack1 fullPreludeEnv fuel St.init mutatingItem).2.world.selfExtra
      = [Atom.sym "A"] := by
  simp [interpretStack1, mutatingItem, spaceName, St.mapWorld, resolveTok,
    World.appendSelf, St.init, World.empty, Metta.instantiate_nil]

/-- Consequently NO certificate can cover the mutating item: any invariant
containing it would violate the `preserves` obligation. -/
theorem no_certificate_covers_mutation
    (Inv : World → Item → Prop)
    (cert : Certificate fullPreludeEnv Inv) :
    ¬ Inv St.init.world mutatingItem := by
  intro hinv
  have preserved := cert.preserves 0 St.init mutatingItem hinv
  have written := mutatingItem_step_writes_world 0
  rw [preserved] at written
  simp [St.init, World.empty] at written

/-! ### The strict global profile is strictly stronger

The criterion below is what demotes environment-level closure: a single
declaration outside the fragment refutes it for the whole environment, however
few runs ever reach that declaration. -/

/-- One offending declaration refutes the whole profile. -/
theorem not_strictGlobalProfile_of_mem {env : MinEnv} {a : Atom}
    (hmem : a ∈ env.atoms) (hbad : ¬ StateOpFree a) :
    ¬ StrictGlobalProfile env := by
  intro profile
  exact hbad (stateOpFree_of_mem profile.environment.atoms hmem)

/-- The prelude's own `add-atom` type declaration, verbatim. -/
def preludeAddAtomDeclaration : Atom :=
  Atom.expr [Atom.sym ":", Atom.sym "add-atom",
    Atom.expr [Atom.sym "->", Atom.sym "SpaceType", Atom.sym "Atom",
      Atom.expr [Atom.sym "->"]]]

/-- It is outside the fragment, because `add-atom` occurs in it as a symbol. -/
theorem preludeAddAtomDeclaration_not_stateOpFree :
    ¬ StateOpFree preludeAddAtomDeclaration := by
  rintro ⟨-, hlist⟩
  exact absurd hlist.2.1 (by simp [StateOpFree, worldMutatingHeads])

/-- **Any environment carrying that declaration fails the strict profile** —
including the shipped prelude, which declares it exactly once.  The prelude
instance is stated at this remove because `preludeAtoms` is produced by running
the parser over the prelude source, and kernel-reducing that parse is not
viable; the criterion is therefore proved in the general form that applies to
it. -/
theorem not_strictGlobalProfile_of_declares_addAtom {env : MinEnv}
    (hmem : preludeAddAtomDeclaration ∈ env.atoms) :
    ¬ StrictGlobalProfile env :=
  not_strictGlobalProfile_of_mem hmem preludeAddAtomDeclaration_not_stateOpFree

end Mettapedia.Languages.MeTTa.HE.StateFreeExecution
