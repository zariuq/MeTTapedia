import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-!
# Equation-invariant active header observations

The occurrence machinery retains origins for execution inversion. Erasing
only those origins gives a static observation of active input/output headers,
their subjects and ordered output fields. This forgets multiplicity, not
channel identity or arity. Input bodies stay opaque and private binders are
interpreted by the supplied private marker.

All structural equations preserve this observation, including contraction of
copied guards into a persistent server. Public predicates distinguish a
queried ambient name from the private marker and inhabit the existing native
logic of the operational theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservation

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveMarkedNames

universe u

def observations {Key : Type u} {Γ : Ctx sig} (fresh : Key)
    (environment : Environment Key Γ) (process : Proc Γ) : Set (Observation Unit Key) :=
  observe (fun _ : Unit => fresh) (ActiveSyntaxMarking.mark () process) process environment

/-- After forgetting origins, every fitted marking computes the same
observation. This uses the actual process and every actual header field. -/
theorem fitted_observe {Key : Type u} {Γ : Ctx sig} {marked : ActiveMarking.Tree Unit} {process : Proc Γ}
    (fits : Fits marked process) (fresh : Key) : ∀ environment : Environment Key Γ,
    observe (fun _ : Unit => fresh) marked process environment =
      observations fresh environment process := by
  induction fits with
  | var => intro environment; simp only [observe, observations, ActiveSyntaxMarking.mark]
  | nil => intro environment; simp only [nil, observe, observations, ActiveSyntaxMarking.mark]
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, observe, observations, ActiveSyntaxMarking.mark]
      exact congrArg₂ Set.union (firstIH environment) (secondIH environment)
  | inp1 origin channel =>
      intro environment; cases origin
      simp only [inp1, observe, observations, ActiveSyntaxMarking.mark]
  | inp2 origin channel =>
      intro environment; cases origin
      simp only [inp2, observe, observations, ActiveSyntaxMarking.mark]
  | out1 origin channel datum =>
      intro environment; cases origin
      simp only [out1, observe, observations, ActiveSyntaxMarking.mark]
  | out2 origin channel first second =>
      intro environment; cases origin
      simp only [out2, observe, observations, ActiveSyntaxMarking.mark]
  | nu origin _ ih =>
      intro environment
      cases origin
      simpa only [nu, observe, observations, ActiveSyntaxMarking.mark] using
        ih (extend fresh environment)
  | rep _ ih =>
      intro environment
      simpa only [rep, observe, observations, ActiveSyntaxMarking.mark] using ih environment

/-- The bidirectional structural lift and its actual occurrence-inclusion
theorem give equality once occurrence origins are forgotten. -/
theorem observations_structural {Key : Type u} {Γ : Ctx sig} (fresh : Key)
    (environment : Environment Key Γ) {first second : Proc Γ}
    (equal : StructuralEq first second) :
    observations fresh environment first = observations fresh environment second := by
  obtain ⟨forwardMark, forwardFits, forward⟩ :=
    (structural_lift () equal).1 _ (ActiveSyntaxMarking.mark_fits () first)
  obtain ⟨backwardMark, backwardFits, backward⟩ :=
    (structural_lift () equal).2 _ (ActiveSyntaxMarking.mark_fits () second)
  apply Set.Subset.antisymm
  · have back := ActiveMarkedNames.Transport.observations_back (fun _ : Unit => fresh) backward environment
    rw [fitted_observe backwardFits fresh] at back
    exact back
  · have back := ActiveMarkedNames.Transport.observations_back (fun _ : Unit => fresh) forward environment
    rw [fitted_observe forwardFits fresh] at back
    exact back

def HasHeader {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (process : Proc Γ) : Prop :=
  ∃ fields, (⟨kind, (), subject, fields⟩ : Observation Unit Key) ∈
    observations fresh environment process

theorem hasHeader_par {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (first second : Proc Γ) :
    HasHeader kind subject fresh environment (par first second) ↔
      HasHeader kind subject fresh environment first ∨ HasHeader kind subject fresh environment second := by
  simp only [HasHeader, observations, par, ActiveSyntaxMarking.mark, observe, Set.mem_union, exists_or]

theorem hasHeader_nu {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (body : Proc (.nm :: Γ)) :
    HasHeader kind subject fresh environment (nu body) ↔
      HasHeader kind subject fresh (extend fresh environment) body := by
  simp only [HasHeader, observations, nu, ActiveSyntaxMarking.mark, observe]

theorem hasHeader_rep {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (body : Proc Γ) :
    HasHeader kind subject fresh environment (rep body) ↔ HasHeader kind subject fresh environment body := by
  simp only [HasHeader, observations, rep, ActiveSyntaxMarking.mark, observe]

theorem hasHeader_inp1 {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (channel : Name Γ) (body : Proc (.nm :: Γ)) :
    HasHeader kind subject fresh environment (inp1 channel body) ↔
      kind = .input1 ∧ subject = nameKey environment channel := by
  simp [HasHeader, observations, inp1, ActiveSyntaxMarking.mark, observe, Observation.mk.injEq]

theorem hasHeader_inp2 {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    HasHeader kind subject fresh environment (inp2 channel body) ↔
      kind = .input2 ∧ subject = nameKey environment channel := by
  simp [HasHeader, observations, inp2, ActiveSyntaxMarking.mark, observe, Observation.mk.injEq]

theorem hasHeader_out1 {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (channel datum : Name Γ) :
    HasHeader kind subject fresh environment (out1 channel datum) ↔
      kind = .output1 ∧ subject = nameKey environment channel := by
  simp [HasHeader, observations, out1, ActiveSyntaxMarking.mark, observe, Observation.mk.injEq]

theorem hasHeader_out2 {Key : Type u} {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject fresh : Key) (environment : Environment Key Γ) (channel first second : Name Γ) :
    HasHeader kind subject fresh environment (out2 channel first second) ↔
      kind = .output2 ∧ subject = nameKey environment channel := by
  simp [HasHeader, observations, out2, ActiveSyntaxMarking.mark, observe, Observation.mk.injEq]

theorem hasHeader_structural {Key : Type u} {Γ : Ctx sig}
    (kind : ActiveHeaderInvariant.Header) (subject fresh : Key)
    (environment : Environment Key Γ) {first second : Proc Γ}
    (equal : StructuralEq first second) :
    HasHeader kind subject fresh environment first ↔
      HasHeader kind subject fresh environment second := by
  unfold HasHeader
  rw [observations_structural fresh environment equal]

/-- The private marker has an additional context position, distinct from
every ambient subject independently of any name enumeration. -/
def PublicHeader {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header)
    (subject : Var Γ .nm) (process : Proc Γ) : Prop :=
  HasHeader kind (Var.succ subject) (Var.zero : Var (.nm :: Γ) .nm)
    (fun name => Var.succ name) process

def predicate {Γ : Ctx sig} (kind : ActiveHeaderInvariant.Header) (subject : Var Γ .nm) :
    EquationPredicate (NativeTypes.operationalTheory Γ) :=
  ⟨PublicHeader kind subject,
    fun _ _ equal => hasHeader_structural kind _ _ _ equal⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservation
