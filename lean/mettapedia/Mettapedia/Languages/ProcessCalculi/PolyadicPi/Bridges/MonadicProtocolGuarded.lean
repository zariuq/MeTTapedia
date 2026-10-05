import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

/-!
# Guarded source processes for the private unary protocol

Both communication arities are retained in this syntactic source fragment.
Every input continuation belongs to the same fragment, and replication has
an input prefix at its head. Parallel composition and restriction remain
available in continuations. The existing active-frontier normalization
therefore exposes only messages, listeners and persistent listeners.

This is a grammar for canonical source processes, rather than a predicate
claimed to hold of every structurally equivalent presentation. In particular,
structural equations can insert a parallel unit inside a replicated guard.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ScopedActiveFrontier

/-- The source grammar admits both arities and recursively guarded bodies.
Replicated restrictions and replicated autonomous processes are excluded. -/
inductive Guarded : {Γ : Ctx sig} → Proc Γ → Prop where
  | nil {Γ} : Guarded (nil : Proc Γ)
  | par {Γ} {first second : Proc Γ} :
      Guarded first → Guarded second → Guarded (par first second)
  | nu {Γ} {body : Proc (.nm :: Γ)} : Guarded body → Guarded (nu body)
  | inp1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Guarded body → Guarded (inp1 channel body)
  | inp2 {Γ} (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)} :
      Guarded body → Guarded (inp2 channel body)
  | out1 {Γ} (channel datum : Name Γ) : Guarded (out1 channel datum)
  | out2 {Γ} (channel first second : Name Γ) : Guarded (out2 channel first second)
  | server1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Guarded body → Guarded (rep (inp1 channel body))
  | server2 {Γ} (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)} :
      Guarded body → Guarded (rep (inp2 channel body))

theorem Guarded.rename {Γ Δ : Ctx sig} {process : Proc Γ}
    (guarded : Guarded process) (environment : Ren sig Γ Δ) :
    Guarded (Mettapedia.OSLF.Binding.rename environment process) := by
  induction guarded generalizing Δ with
  | nil => exact .nil
  | par _ _ firstIH secondIH => exact .par (firstIH environment) (secondIH environment)
  | nu _ ih => exact .nu (ih (liftRen environment [.nm]))
  | inp1 channel _ ih => exact .inp1 _ (ih (liftRen environment [.nm]))
  | inp2 channel _ ih => exact .inp2 _ (ih (liftRen environment [.nm, .nm]))
  | out1 => exact .out1 _ _
  | out2 => exact .out2 _ _ _
  | server1 channel _ ih => exact .server1 _ (ih (liftRen environment [.nm]))
  | server2 channel _ ih => exact .server2 _ (ih (liftRen environment [.nm, .nm]))

/-- Guarded processes have no free process-variable leaves. Arbitrary
substitution of their names consequently preserves the guarded grammar. -/
theorem Guarded.bind {Γ Δ : Ctx sig} {process : Proc Γ}
    (guarded : Guarded process) (environment : Sub sig Γ Δ) :
    Guarded (Mettapedia.OSLF.Binding.bind environment process) := by
  induction guarded generalizing Δ with
  | nil => exact .nil
  | par _ _ firstIH secondIH => exact .par (firstIH environment) (secondIH environment)
  | nu _ ih => exact .nu (ih (liftSub environment [.nm]))
  | inp1 channel _ ih => exact .inp1 _ (ih (liftSub environment [.nm]))
  | inp2 channel _ ih => exact .inp2 _ (ih (liftSub environment [.nm, .nm]))
  | out1 => exact .out1 _ _
  | out2 => exact .out2 _ _ _
  | server1 channel _ ih => exact .server1 _ (ih (liftSub environment [.nm]))
  | server2 channel _ ih => exact .server2 _ (ih (liftSub environment [.nm, .nm]))

/-- A unary receipt activates a body within the same source domain. -/
theorem Guarded.inst {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : Guarded body) (datum : Name Γ) : Guarded (inst body datum) :=
  guarded.bind (extend datum)

/-- A binary receipt activates the authored body in the supplied field order. -/
theorem Guarded.openPair {Γ : Ctx sig} {body : Proc (.nm :: .nm :: Γ)}
    (guarded : Guarded body) (first second : Name Γ) :
    Guarded (openPair body first second) := guarded.bind (pairSub first second)

/-- Every clause of the actual lambda compiler has a recursively guarded
image, including stored definitions and one-shot carriers. -/
theorem guarded_compiler_image {Γ Δ : Ctx sig}
    (term : NamePassingLambda.Expr Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) : Guarded (NamePassingLambda.compile term environment result) := by
  induction term generalizing Δ with
  | var => exact .out1 _ _
  | lam body ih => exact .inp2 _ (ih (NamePassingLambda.callEnv environment) (.succ .zero))
  | app function argument ih =>
      exact .nu (.par (ih (NamePassingLambda.push environment) .zero) (.out2 _ _ _))
  | defn value body valueIH bodyIH =>
      exact .nu (.par (bodyIH (liftRen environment [.nm]) (.succ result))
        (.server1 _ (valueIH (NamePassingLambda.push (NamePassingLambda.push environment)) .zero)))
  | carrier name value body valueIH bodyIH =>
      exact .par (bodyIH environment result)
        (.inp1 _ (valueIH (NamePassingLambda.push environment) .zero))

/-- The possible atoms of the existing active-frontier normalization.
Each listener retains its guarded continuation; nothing steps beneath it. -/
inductive GuardedAtom : {Γ : Ctx sig} → Proc Γ → Prop where
  | inp1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Guarded body → GuardedAtom (inp1 channel body)
  | inp2 {Γ} (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)} :
      Guarded body → GuardedAtom (inp2 channel body)
  | out1 {Γ} (channel datum : Name Γ) : GuardedAtom (out1 channel datum)
  | out2 {Γ} (channel first second : Name Γ) : GuardedAtom (out2 channel first second)
  | server1 {Γ} (channel : Name Γ) {body : Proc (.nm :: Γ)} :
      Guarded body → GuardedAtom (rep (inp1 channel body))
  | server2 {Γ} (channel : Name Γ) {body : Proc (.nm :: .nm :: Γ)} :
      Guarded body → GuardedAtom (rep (inp2 channel body))

theorem GuardedAtom.rename {Γ Δ : Ctx sig} {atom : Proc Γ}
    (guarded : GuardedAtom atom) (environment : Ren sig Γ Δ) :
    GuardedAtom (Mettapedia.OSLF.Binding.rename environment atom) := by
  cases guarded with
  | inp1 channel body => exact .inp1 _ (body.rename (liftRen environment [.nm]))
  | inp2 channel body => exact .inp2 _ (body.rename (liftRen environment [.nm, .nm]))
  | out1 => exact .out1 _ _
  | out2 => exact .out2 _ _ _
  | server1 channel body => exact .server1 _ (body.rename (liftRen environment [.nm]))
  | server2 channel body => exact .server2 _ (body.rename (liftRen environment [.nm, .nm]))

theorem GuardedAtom.guarded {Γ : Ctx sig} {atom : Proc Γ}
    (guarded : GuardedAtom atom) : Guarded atom := by
  cases guarded with
  | inp1 channel body => exact .inp1 _ body
  | inp2 channel body => exact .inp2 _ body
  | out1 => exact .out1 _ _
  | out2 => exact .out2 _ _ _
  | server1 channel body => exact .server1 _ body
  | server2 channel body => exact .server2 _ body

/-- Normalization keeps a finite list of actual guarded communication heads.
The existing merge reindexes each selected occurrence into its common world. -/
theorem Guarded.normalized_atoms {Γ : Ctx sig} {process : Proc Γ}
    (guarded : Guarded process) :
    ∀ atom ∈ (normalize process).atoms, GuardedAtom atom := by
  induction guarded with
  | nil =>
      rw [normalize_nil]
      intro atom member
      exact False.elim (List.not_mem_nil member)
  | par first second firstIH secondIH =>
      rw [normalize_par]
      intro atom member
      change atom ∈ (ScopedActiveFrontier.normalize _).atoms.map
        (Mettapedia.OSLF.Binding.rename
          (mergeLeft (ScopedActiveFrontier.normalize _) (ScopedActiveFrontier.normalize _))) ++
        (ScopedActiveFrontier.normalize _).atoms.map
          (Mettapedia.OSLF.Binding.rename
            (mergeRight (ScopedActiveFrontier.normalize _) (ScopedActiveFrontier.normalize _)))
        at member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
        subst atom
        exact (firstIH old oldMember).rename _
      · obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
        subst atom
        exact (secondIH old oldMember).rename _
  | nu body ih =>
      rw [normalize_nu]
      exact ih
  | inp1 channel body =>
      rw [normalize_inp1]
      intro atom member
      have equal : atom = PolyadicPi.inp1 channel _ := List.mem_singleton.mp member
      subst atom
      exact .inp1 channel body
  | inp2 channel body =>
      rw [normalize_inp2]
      intro atom member
      have equal : atom = PolyadicPi.inp2 channel _ := List.mem_singleton.mp member
      subst atom
      exact .inp2 channel body
  | out1 channel datum =>
      rw [normalize_out1]
      intro atom member
      have equal : atom = PolyadicPi.out1 channel datum := List.mem_singleton.mp member
      subst atom
      exact .out1 _ _
  | out2 channel first second =>
      rw [normalize_out2]
      intro atom member
      have equal : atom = PolyadicPi.out2 channel first second := List.mem_singleton.mp member
      subst atom
      exact .out2 _ _ _
  | server1 channel body =>
      rw [normalize_rep]
      intro atom member
      have equal : atom = rep (PolyadicPi.inp1 channel _) := List.mem_singleton.mp member
      subst atom
      exact .server1 _ body
  | server2 channel body =>
      rw [normalize_rep]
      intro atom member
      have equal : atom = rep (PolyadicPi.inp2 channel _) := List.mem_singleton.mp member
      subst atom
      exact .server2 _ body

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
