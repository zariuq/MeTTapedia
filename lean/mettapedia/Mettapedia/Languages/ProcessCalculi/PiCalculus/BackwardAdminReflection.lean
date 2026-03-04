import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization

/-!
# Backward Admin Reflection (π→ρ, Derived Layer)

This module starts the backward side by packaging reflected structure from the
proved non-RF administrative forward closure:

- encoded-image closure up to structural congruence (`EncodedSC`)
- reflected witnesses for combined ν/seed/replicate administrative traces
- concrete and nontrivial canaries
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-- Encoded image closed under ρ structural congruence. -/
def EncodedSC (n v : String) (p : Pattern) : Prop :=
  ∃ p0, EncodingMorphism.Encoded n v p0 ∧
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p p0

/-- Any directly encoded term is in `EncodedSC`. -/
theorem encodedSC_of_encoded {n v : String} {p : Pattern}
    (h : EncodingMorphism.Encoded n v p) : EncodedSC n v p :=
  ⟨p, h, Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _⟩

/-- Encoding outputs are in `EncodedSC`. -/
theorem encode_is_EncodedSC (P : Process) (n v : String) :
    EncodedSC n v (encode P n v) :=
  encodedSC_of_encoded (EncodingMorphism.encode_is_Encoded P n v)

/-- `EncodedSC` is stable under left structural congruence transport. -/
theorem EncodedSC.of_sc {n v : String} {p q : Pattern}
    (hp : EncodedSC n v p)
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q) :
    EncodedSC n v q := by
  rcases hp with ⟨p0, henc, hp0⟩
  refine ⟨p0, henc, ?_⟩
  exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.trans
    _ _ _ (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsc) hp0

/-- Non-RF admin-layer sources used in π→ρ derived correspondence. -/
inductive AdminSource : Pattern → Prop where
  | nuListener (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
      AdminSource
        (rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda listenerBody]))
  | seedListener (x z v s : String) (listenerBody : Pattern) :
      AdminSource
        (rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda listenerBody]))
  | replicate (x y : Name) (P : Process) (n v : String) :
      AdminSource (encode (.replicate x y P) n v)


/-- Canonical admin targets paired with `AdminSource` terms. -/
inductive AdminCanonicalTarget : Pattern → Pattern → Prop where
  | nuListener (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
      AdminCanonicalTarget
        (rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda listenerBody]))
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none)
  | seedListener (x z v s : String) (listenerBody : Pattern) :
      AdminCanonicalTarget
        (rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda listenerBody]))
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none)
  | replicate (x y : Name) (P : Process) (n v : String) :
      AdminCanonicalTarget
        (encode (.replicate x y P) n v)
        (rhoPar
          (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))
          (encode (.replicate x y P) n v))

/-- First backward theorem endpoint for non-RF admin sources:
derived progress to a canonical admin target up to derived weak bisimilarity. -/
theorem admin_source_forward_progress {N : Finset String} {src : Pattern}
    (hsrc : AdminSource src) :
    ∃ tgt canon, Nonempty (src ⇝ᵈ* tgt) ∧
      AdminCanonicalTarget src canon ∧
      tgt ≈ᵈ{N} canon := by
  cases hsrc with
  | nuListener x P n v listenerBody =>
      rcases forward_single_step_nu_listener_derived
          (N := N) x P n v listenerBody with ⟨tgt, hstep, hbisim⟩
      exact ⟨tgt,
        .collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none,
        hstep, AdminCanonicalTarget.nuListener x P n v listenerBody, hbisim⟩
  | seedListener x z v s listenerBody =>
      rcases forward_single_step_nameServer_listener_derived
          (N := N) x z v s listenerBody with ⟨tgt, hstep, hbisim⟩
      exact ⟨tgt,
        .collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none,
        hstep, AdminCanonicalTarget.seedListener x z v s listenerBody, hbisim⟩
  | replicate x y P n v =>
      rcases forward_single_step_replicate_derived
          (N := N) x y P n v with ⟨tgt, hstep, hbisim⟩
      exact ⟨tgt,
        rhoPar
          (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))
          (encode (.replicate x y P) n v),
        hstep, AdminCanonicalTarget.replicate x y P n v, hbisim⟩

/-- Weak backward reflection outcomes for non-RF admin sources.
The second branch is reserved for direct π-step reflection once proved. -/
inductive WeakBackwardOutcome (N : Finset String) (src : Pattern) : Prop where
  | adminProgress :
      (tgt : Pattern) →
      (canon : Pattern) →
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      AdminCanonicalTarget src canon →
      WeakRestrictedBisimD N tgt canon →
      WeakBackwardOutcome N src
  | piStep :
      (P P' : Process) →
      (n v : String) →
      (tgt : Pattern) →
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) →
      Nonempty (P ⇝ P') →
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar (encode P n v) tgt) →
      WeakRestrictedBisimD N tgt (encode P' n v) →
      WeakBackwardOutcome N src

/-- Weak backward outcomes paired with an explicit disjointness condition
for a chosen seed-name set. -/
def WeakBackwardOutcomeFreshAt
    (N : Finset String) (src : Pattern) (seeds : Finset Name) : Prop :=
  Disjoint N seeds ∧ WeakBackwardOutcome N src

/-- Convenience alias for full-encode reserved-name freshness. -/
abbrev WeakBackwardOutcomeFresh (N : Finset String) (src : Pattern) : Prop :=
  WeakBackwardOutcomeFreshAt N src fullEncodeReservedNames

/-- Observation-set weakening for weak backward outcomes. -/
theorem WeakBackwardOutcome.mono {N N' : Finset String} {src : Pattern}
    (h : WeakBackwardOutcome N src) (hsub : N' ⊆ N) :
    WeakBackwardOutcome N' src := by
  cases h with
  | adminProgress tgt canon hstep hcanon hbisim =>
      exact WeakBackwardOutcome.adminProgress tgt canon hstep hcanon
        (WeakRestrictedBisimD.mono hbisim hsub)
  | piStep P P' n v tgt hsrcSC hpi hstep hbisim =>
      exact WeakBackwardOutcome.piStep P P' n v tgt hsrcSC hpi hstep
        (WeakRestrictedBisimD.mono hbisim hsub)

/-- SC-source adequacy wrapper for `piStep` outcomes:
if a source is SC-equivalent to an encoded π term, it can be reflected via the
`piStep` branch using the encoded-source derived trace witness. -/
theorem weak_backward_outcome_piStep_of_SC_source
    {N : Finset String} {src tgt : Pattern}
    (P P' : Process) (n v : String)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode P n v))
    (hpi : Nonempty (P ⇝ P'))
    (hstep : Nonempty
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar
        (encode P n v) tgt))
    (hbisim : WeakRestrictedBisimD N tgt (encode P' n v)) :
    WeakBackwardOutcome N src := by
  exact WeakBackwardOutcome.piStep P P' n v tgt hsrcSC hpi hstep hbisim

private theorem hasDerivedHead_elem_false_of_any_false
    {elems : List Pattern} {e : Pattern}
    (hany : (elems.map Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead).any
      (fun b => b) = false)
    (he : e ∈ elems) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false := by
  by_cases hfalse :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false
  · exact hfalse
  · have htrue :
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = true := by
      cases hbe :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e with
      | false =>
          exact False.elim (hfalse hbe)
      | true =>
          rfl
    have hmemTrue : true ∈ elems.map
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead := by
      exact List.mem_map.mpr ⟨e, he, by simp [htrue]⟩
    have hanyTrue :
        (elems.map Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead).any
          (fun b => b) = true := by
      exact List.any_eq_true.mpr ⟨true, by simpa [htrue] using hmemTrue, rfl⟩
    simp [hany] at hanyTrue

private theorem hasDerivedHead_closeFVar_false {k : Nat} {x : String} {p : Pattern}
    (hp : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead p = false) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
      (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar k x p) = false := by
  suffices h :
      ∀ (p : Pattern) (k : Nat),
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead p = false →
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
            (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar k x p) = false from
    h p k hp
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro k hp'
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead]
  | hfvar y =>
      intro k hp'
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar]
      split_ifs <;>
      simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead]
  | happly c args ih =>
      intro k hp'
      by_cases hrep : c = "PReplicate"
      · subst hrep
        simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] at hp'
      by_cases hnu : c = "PNu"
      · subst hnu
        simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] at hp'
      · have hany :
            (args.map Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead).any
              (fun b => b) = false := by
          simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead, hrep, hnu]
            using hp'
        have hall :
            ∀ a ∈ args,
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead a = false := by
          intro a ha
          exact hasDerivedHead_elem_false_of_any_false hany ha
        have hallCloseMap :
            ∀ e ∈ args.map (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar k x),
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false := by
          intro e he
          rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
          exact ih a ha k (hall a ha)
        have hanyClose :
            ((args.map (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar k x)).map
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead).any
                (fun b => b) = false := by
          exact
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead_any_false_of_forall_false
              hallCloseMap
        simpa [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead, hrep, hnu] using
          hanyClose
  | hlambda body ih =>
      intro k hp'
      have hbody :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead body = false := by
        simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] using hp'
      have hclose :=
        ih (k + 1) hbody
      simpa [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] using hclose
  | hmultiLambda n body ih =>
      intro k hp'
      have hbody :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead body = false := by
        simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] using hp'
      have hclose :=
        ih (k + n) hbody
      simpa [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] using hclose
  | hsubst body repl ihBody ihRepl =>
      intro k hp'
      have hparts :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead body = false ∧
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead repl = false := by
        simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead,
          Bool.or_eq_false_iff] using hp'
      have hbodyClose :=
        ihBody (k + 1) hparts.1
      have hreplClose :=
        ihRepl k hparts.2
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead,
        hbodyClose, hreplClose]
  | hcollection ct elems rest ih =>
      intro k hp'
      have hany :
          (elems.map Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead).any
            (fun b => b) = false := by
        simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] using hp'
      have hall :
          ∀ a ∈ elems,
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead a = false := by
        intro a ha
        exact hasDerivedHead_elem_false_of_any_false hany ha
      have hallCloseMap :
          ∀ e ∈ elems.map (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar k x),
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false := by
        intro e he
        rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
        exact ih a ha k (hall a ha)
      have hanyClose :
          ((elems.map (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar k x)).map
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead).any
              (fun b => b) = false := by
        exact
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead_any_false_of_forall_false
            hallCloseMap
      simpa [Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead] using hanyClose

private theorem rhoPar_eq_parComponents_append (p q : Pattern) :
    rhoPar p q = .collection .hashBag
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents p ++
       Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents q) none := by
  cases p <;> cases q
  all_goals
    first
    | rfl
    | cases ‹CollType› <;> cases ‹Option String› <;> rfl
    | cases ‹CollType› <;> cases ‹Option String› <;> cases ‹CollType› <;> cases ‹Option String› <;> rfl

private theorem hasDerivedHead_parComponents_false_of_false {p : Pattern}
    (hp : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead p = false) :
    ∀ e ∈ Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents p,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false := by
  intro e he
  cases p
  all_goals
    first
    | simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at he
      rcases he with rfl
      simpa using hp
    | cases ‹CollType› <;> cases ‹Option String›
      · simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at he
        rcases he with rfl
        simpa using hp
      · simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at he
        rcases he with rfl
        simpa using hp
      · have hc :
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
              (.collection .hashBag ‹List Pattern› none) := by
          simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical] using hp
        simpa [Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical] using
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.coreCanonical_elem_of_collection
            (ct := .hashBag) (elems := ‹List Pattern›) (e := e) hc he)
      · simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at he
        rcases he with rfl
        simpa using hp
      · simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at he
        rcases he with rfl
        simpa using hp
      · simp [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at he
        rcases he with rfl
        simpa using hp

private theorem hasDerivedHead_collection_false_of_forall {elems : List Pattern}
    (hall : ∀ e ∈ elems,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
      (.collection .hashBag elems none) = false := by
  unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
  simpa using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead_any_false_of_forall_false hall)

private theorem hasDerivedHead_rhoPar_false (p q : Pattern)
    (hp : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead p = false)
    (hq : Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead q = false) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead (rhoPar p q) = false := by
  have hpAll : ∀ e ∈ Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents p,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false :=
    hasDerivedHead_parComponents_false_of_false hp
  have hqAll : ∀ e ∈ Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents q,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false :=
    hasDerivedHead_parComponents_false_of_false hq
  have hall : ∀ e ∈
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents p ++
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents q,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead e = false := by
    intro e he
    rcases List.mem_append.mp he with hmem | hmem
    · exact hpAll e hmem
    · exact hqAll e hmem
  rw [rhoPar_eq_parComponents_append]
  exact hasDerivedHead_collection_false_of_forall hall

private theorem hasDerivedHead_encode_rf {P : Process}
    (hrf : ForwardSimulation.RestrictionFree P) :
    ∀ n v,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
        (encode P n v) = false := by
  induction P with
  | nil =>
      intro n v
      simp [encode, rhoNil,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead]
  | par P Q ihP ihQ =>
      intro n v
      have hrfPQ : ForwardSimulation.RestrictionFree P ∧ ForwardSimulation.RestrictionFree Q := by
        simpa [ForwardSimulation.RestrictionFree] using hrf
      have hP :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
            (encode P (n ++ "_L") v) = false :=
        ihP hrfPQ.1 (n ++ "_L") v
      have hQ :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
            (encode Q (n ++ "_R") v) = false :=
        ihQ hrfPQ.2 (n ++ "_R") v
      exact hasDerivedHead_rhoPar_false (encode P (n ++ "_L") v) (encode Q (n ++ "_R") v) hP hQ
  | input x y P ih =>
      intro n v
      have hrfP : ForwardSimulation.RestrictionFree P := by
        simpa [ForwardSimulation.RestrictionFree] using hrf
      have hBody :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
            (encode P n v) = false :=
        ih hrfP n v
      have hClose :
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead
            (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v)) = false :=
        hasDerivedHead_closeFVar_false hBody
      simp [encode, rhoInput,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead,
        hClose, piNameToRhoName]
  | output x z =>
      intro n v
      simp [encode, rhoOutput, rhoDrop, piNameToRhoName,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.hasDerivedHead]
  | nu x P ih =>
      cases hrf
  | replicate x y P ih =>
      cases hrf

private theorem reducesRF_to_reduces
    {P Q : Process} (h : ForwardSimulation.ReducesRF P Q) :
    Nonempty (P ⇝ Q) := by
  induction h with
  | comm x y z R =>
      exact ⟨Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduces.comm x y z R⟩
  | par_left P P' R h ih =>
      rcases ih with ⟨h'⟩
      exact ⟨Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduces.par_left P P' R h'⟩
  | par_right P Q Q' h ih =>
      rcases ih with ⟨h'⟩
      exact ⟨Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduces.par_right P Q Q' h'⟩
  | struct P P' Q Q' hsc₁ hred hsc₂ ih =>
      rcases ForwardSimulation.rfsc_to_sc hsc₁ with ⟨hsc₁'⟩
      rcases ih with ⟨h'⟩
      rcases ForwardSimulation.rfsc_to_sc hsc₂ with ⟨hsc₂'⟩
      exact ⟨Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduces.struct P P' Q Q' hsc₁' h' hsc₂'⟩

/-- Any RF one-step has a reflected `piStep` outcome in the derived backward
layer at arbitrary encoding seeds/channels `(n,v)`. -/
theorem weak_backward_outcome_piStep_rf_step_at
    {N : Finset String} {P Q : Process}
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (n v : String) :
    WeakBackwardOutcome N (encode P n v) := by
  have hpi : Nonempty (P ⇝ Q) := reducesRF_to_reduces h
  rcases ForwardSimulation.forward_single_step_rf h hrf hsafe n v with
    ⟨tgt, hstepCore, hscTgt⟩
  have hstepDerived :
      Nonempty ((encode P n v) ⇝ᵈ* tgt) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived
      (Classical.choice hstepCore)⟩
  have hrfQ : ForwardSimulation.RestrictionFree Q :=
    ForwardSimulation.reducesRF_preserves_rf h hrf
  have hcanonEncodeQ :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
        (encode Q n v) := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
    simpa using hasDerivedHead_encode_rf hrfQ n v
  have hcanonTgt :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical tgt := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.coreCanonical_of_SC
        hcanonEncodeQ
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hscTgt)
  have hbisim : tgt ≈ᵈ{N} (encode Q n v) := by
    exact WeakRestrictedBisimD.of_SC_coreCanonical
      (N := N) (p := tgt) (q := encode Q n v) hscTgt hcanonTgt
  exact WeakBackwardOutcome.piStep
    P Q n v tgt
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
    hpi hstepDerived hbisim

/-- SC-source lift for arbitrary RF one-step reflected `piStep` outcomes
at arbitrary encoding seeds/channels `(n,v)`. -/
theorem weak_backward_outcome_piStep_rf_step_of_SC_source_at
    {N : Finset String} {P Q : Process} {src : Pattern}
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (n v : String)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v)) :
    WeakBackwardOutcome N src := by
  have hpi : Nonempty (P ⇝ Q) := reducesRF_to_reduces h
  rcases ForwardSimulation.forward_single_step_rf h hrf hsafe n v with
    ⟨tgt, hstepCore, hscTgt⟩
  have hstepDerived :
      Nonempty ((encode P n v) ⇝ᵈ* tgt) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived
      (Classical.choice hstepCore)⟩
  have hrfQ : ForwardSimulation.RestrictionFree Q :=
    ForwardSimulation.reducesRF_preserves_rf h hrf
  have hcanonEncodeQ :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
        (encode Q n v) := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
    simpa using hasDerivedHead_encode_rf hrfQ n v
  have hcanonTgt :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical tgt := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.coreCanonical_of_SC
        hcanonEncodeQ
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hscTgt)
  have hbisim : tgt ≈ᵈ{N} (encode Q n v) := by
    exact WeakRestrictedBisimD.of_SC_coreCanonical
      (N := N) (p := tgt) (q := encode Q n v) hscTgt hcanonTgt
  exact weak_backward_outcome_piStep_of_SC_source
    (P := P) (P' := Q) (n := n) (v := v) hsrcSC hpi hstepDerived hbisim

/-- Backward-compatible fixed-seed wrapper for RF one-step `piStep` reflection. -/
theorem weak_backward_outcome_piStep_rf_step
    {N : Finset String} {P Q : Process}
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h) :
    WeakBackwardOutcome N (encode P "n_init" "v_init") := by
  simpa using weak_backward_outcome_piStep_rf_step_at
    (N := N) (P := P) (Q := Q) h hrf hsafe "n_init" "v_init"

/-- Weak backward reflection (non-RF admin layer):
an encoded/admin source reflects to administrative progress or a corresponding π-step.
Current closure is established by the administrative branch. -/
theorem weak_backward_reflection_nonRF_admin {N : Finset String} {src : Pattern}
    (hsrc : AdminSource src) :
    WeakBackwardOutcome N src := by
  rcases admin_source_forward_progress (N := N) hsrc with
    ⟨tgt, canon, hstep, hcanon, hbisim⟩
  exact WeakBackwardOutcome.adminProgress tgt canon hstep hcanon hbisim

/-- Freshness + user-observation discipline for ν-listener admin sources:
bundles disjointness of reserved names with the backward admin outcome. -/
theorem weak_backward_reflection_nonRF_admin_nu_fresh_userObs
    {N : Finset String} (x : Name) (P : Process) (listenerBody : Pattern)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    WeakBackwardOutcomeFreshAt N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda listenerBody]))
      fullEncodeReservedNames := by
  have hdisj : Disjoint N fullEncodeReservedNames :=
    obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh
  have hout :
      WeakBackwardOutcome N
        (rhoPar (encode (.nu x P) "n_init" "v_init")
          (.apply "PInput" [.fvar "v_init", .lambda listenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N)
      (src := rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda listenerBody]))
      (AdminSource.nuListener x P "n_init" "v_init" listenerBody)
  exact ⟨hdisj, hout⟩

/-- Freshness + user-observation discipline for seed-listener admin sources:
bundles disjointness of reserved names with the backward admin outcome. -/
theorem weak_backward_reflection_nonRF_admin_seed_fresh_userObs
    {N : Finset String} (P : Process) (listenerBody : Pattern)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    WeakBackwardOutcomeFreshAt N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda listenerBody]))
      fullEncodeReservedNames := by
  have hdisj : Disjoint N fullEncodeReservedNames :=
    obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh
  have hout :
      WeakBackwardOutcome N
        (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
          (.apply "PInput" [.fvar "ns_z", .lambda listenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N)
      (src := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda listenerBody]))
      (AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" listenerBody)
  exact ⟨hdisj, hout⟩

/-- Freshness + user-observation discipline for replicate admin sources:
bundles disjointness of the chosen seed pair with the backward admin outcome. -/
theorem weak_backward_reflection_nonRF_admin_replicate_freshAt_userObs
    {N : Finset String} (x y : Name) (P : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFreshAt P n v) :
    WeakBackwardOutcomeFreshAt N (encode (.replicate x y P) n v)
      ({ n, v } : Finset Name) := by
  have hdisj : Disjoint N ({ n, v } : Finset Name) :=
    obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v) hobs hfresh
  have hout : WeakBackwardOutcome N (encode (.replicate x y P) n v) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := encode (.replicate x y P) n v)
      (AdminSource.replicate x y P n v)
  exact ⟨hdisj, hout⟩

/-- Admin sources equipped with user-observation discipline and freshness
assumptions needed to derive disjointness of reserved names. -/
inductive AdminSourceFresh (N : Finset String) : Pattern → Prop where
  | nuListener (x : Name) (P : Process) (listenerBody : Pattern)
      (hobs : N ⊆ P.freeNames)
      (hfresh : EncodingFresh P) :
      AdminSourceFresh N
        (rhoPar (encode (.nu x P) "n_init" "v_init")
          (.apply "PInput" [.fvar "v_init", .lambda listenerBody]))
  | seedListener (P : Process) (listenerBody : Pattern)
      (hobs : N ⊆ P.freeNames)
      (hfresh : EncodingFresh P) :
      AdminSourceFresh N
        (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
          (.apply "PInput" [.fvar "ns_z", .lambda listenerBody]))
  | replicate (x y : Name) (P : Process) (n v : String)
      (hobs : N ⊆ P.freeNames)
      (hfresh : EncodingFreshAt P n v) :
      AdminSourceFresh N (encode (.replicate x y P) n v)

/-- Forgetful map from fresh admin sources to plain admin sources. -/
theorem AdminSourceFresh.to_AdminSource
    {N : Finset String} {src : Pattern}
    (h : AdminSourceFresh N src) : AdminSource src := by
  cases h with
  | nuListener x P listenerBody _ _ =>
      exact AdminSource.nuListener x P "n_init" "v_init" listenerBody
  | seedListener _ listenerBody _ _ =>
      exact AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" listenerBody
  | replicate x y P n v _ _ =>
      exact AdminSource.replicate x y P n v

/-- Fresh admin sources yield admin-progress data with explicit disjointness. -/
theorem admin_source_forward_progress_fresh
    {N : Finset String} {src : Pattern}
    (h : AdminSourceFresh N src) :
    ∃ seeds tgt canon,
      Disjoint N seeds ∧
      Nonempty (src ⇝ᵈ* tgt) ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt canon := by
  cases h with
  | nuListener x P listenerBody hobs hfresh =>
      have hdisj : Disjoint N fullEncodeReservedNames :=
        obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh
      rcases admin_source_forward_progress
          (N := N)
          (src := rhoPar (encode (.nu x P) "n_init" "v_init")
            (.apply "PInput" [.fvar "v_init", .lambda listenerBody]))
          (AdminSource.nuListener x P "n_init" "v_init" listenerBody) with
        ⟨tgt, canon, hstep, hcanon, hbisim⟩
      exact ⟨fullEncodeReservedNames, tgt, canon, hdisj, hstep, hcanon, hbisim⟩
  | seedListener P listenerBody hobs hfresh =>
      have hdisj : Disjoint N fullEncodeReservedNames :=
        obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh
      rcases admin_source_forward_progress
          (N := N)
          (src := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
            (.apply "PInput" [.fvar "ns_z", .lambda listenerBody]))
          (AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" listenerBody) with
        ⟨tgt, canon, hstep, hcanon, hbisim⟩
      exact ⟨fullEncodeReservedNames, tgt, canon, hdisj, hstep, hcanon, hbisim⟩
  | replicate x y P n v hobs hfresh =>
      have hdisj : Disjoint N ({ n, v } : Finset Name) :=
        obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v)
          hobs hfresh
      rcases admin_source_forward_progress
          (N := N)
          (src := encode (.replicate x y P) n v)
          (AdminSource.replicate x y P n v) with
        ⟨tgt, canon, hstep, hcanon, hbisim⟩
      exact ⟨({ n, v } : Finset Name), tgt, canon, hdisj, hstep, hcanon, hbisim⟩

/-- Broader step-source classifier:
reuses admin sources and allows generic RF steps through the `rfStepAt` branch. -/
inductive EncodedSCStepSource (N : Finset String) : Pattern → Prop where
  | admin {src : Pattern} :
      AdminSource src →
      EncodedSCStepSource N src
  | rfStepAt {src : Pattern}
      (P Q : Process) (n v : String)
      (h : ForwardSimulation.ReducesRF P Q)
      (hrf : ForwardSimulation.RestrictionFree P)
      (hsafe : ForwardSimulation.CommSafe h)
      (hsrcSC :
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
          src
          (encode P n v)) :
      EncodedSCStepSource N src

/-- EncodedSC step sources equipped with freshness data for both admin and
RF-step branches. -/
inductive EncodedSCStepSourceFresh (N : Finset String) : Pattern → Prop where
  | admin {src : Pattern} :
      AdminSourceFresh N src →
      EncodedSCStepSourceFresh N src
  | rfStepAt {src : Pattern}
      (P Q : Process) (n v : String)
      (h : ForwardSimulation.ReducesRF P Q)
      (hrf : ForwardSimulation.RestrictionFree P)
      (hsafe : ForwardSimulation.CommSafe h)
      (hsrcSC :
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
          src
          (encode P n v))
      (hobs : N ⊆ P.freeNames)
      (hfresh : EncodingFreshAt P n v) :
      EncodedSCStepSourceFresh N src

/-- Forgetful map from fresh EncodedSC step sources to the base classifier. -/
theorem EncodedSCStepSourceFresh.to_EncodedSCStepSource
    {N : Finset String} {src : Pattern}
    (h : EncodedSCStepSourceFresh N src) :
    EncodedSCStepSource N src := by
  cases h with
  | admin hAdmin =>
      exact EncodedSCStepSource.admin (AdminSourceFresh.to_AdminSource hAdmin)
  | rfStepAt P Q n v h hrf hsafe hsrcSC _ _ =>
      exact EncodedSCStepSource.rfStepAt
        (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC

/-- Data package for RF-step sources in the generic branch. -/
def RFStepData (src : Pattern) : Prop :=
  ∃ (P Q : Process) (n v : String) (h : ForwardSimulation.ReducesRF P Q),
    ForwardSimulation.RestrictionFree P ∧
    ForwardSimulation.CommSafe h ∧
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v)

/-- Generic RF-step classifier: any RF step source yields the rfStepAt branch. -/
theorem encodedSC_step_classifier_rfStepAt
    {N : Finset String} {src : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode P n v)) :
    EncodedSCStepSource N src := by
  exact EncodedSCStepSource.rfStepAt
    (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC

/-- Generic fresh RF-step classifier: RF step sources with freshness data
yield the fresh rfStepAt branch. -/
theorem encodedSC_step_classifier_rfStepAt_fresh
    {N : Finset String} {src : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode P n v))
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFreshAt P n v) :
    EncodedSCStepSourceFresh N src := by
  exact EncodedSCStepSourceFresh.rfStepAt
    (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC hobs hfresh

/-- Observation-index monotonicity for the EncodedSC step-source classifier:
classification data can be reused at any observation set. -/
theorem EncodedSCStepSource.mono {N N' : Finset String} {src : Pattern}
    (h : EncodedSCStepSource N src) :
    EncodedSCStepSource N' src := by
  cases h with
  | admin hAdmin =>
      exact EncodedSCStepSource.admin hAdmin
  | rfStepAt P Q n v h hrf hsafe hsrcSC =>
      exact EncodedSCStepSource.rfStepAt
        (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC

/-- Collapse the RF-classification of an encoded source into either admin
progress or a generic RF-step branch. This retires specialized legacy
handling in downstream theorems. -/
theorem EncodedSCStepSource.to_admin_or_rf
    {N : Finset String} {src : Pattern}
    (h : EncodedSCStepSource N src) :
    AdminSource src ∨ RFStepData src := by
  cases h with
  | admin hAdmin =>
      exact Or.inl hAdmin
  | rfStepAt P Q n v h hrf hsafe hsrcSC =>
      exact Or.inr ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩

/-- EncodedSC step-classifier for a direct RF COMM redex: builds the
`rfStepAt` branch and witnesses the core COMM step using component-level
inversion plus `comm_exists_from_parComponents`. -/
theorem encodedSCStepSource_of_rf_comm_candidate
    {N : Finset String} (x y z : Name) (P : Process) (n v : String)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe
      (ForwardSimulation.ReducesRF.comm x y z P)) :
    EncodedSCStepSource N
      (encode (Process.par (Process.input x y P) (Process.output x z)) n v) := by
  let src := encode (Process.par (Process.input x y P) (Process.output x z)) n v
  have hrfSrc :
      ForwardSimulation.RestrictionFree
        (Process.par (Process.input x y P) (Process.output x z)) := by
    simp [ForwardSimulation.RestrictionFree, hrf]
  have hmemIn :
      .apply "PInput"
        [.fvar x,
          .lambda (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P (n ++ "_L") v))]
        ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src := by
    simp [src, encode, rhoPar, rhoInput, rhoOutput, rhoDrop,
      piNameToRhoName,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents]
  have hmemOut :
      .apply "POutput" [.fvar x, rhoDrop (.fvar z)]
        ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src := by
    simp [src, encode, rhoPar, rhoInput, rhoOutput, rhoDrop,
      piNameToRhoName,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents]
  -- Use the canInteract-based COMM witness.
  have _hcomm :
      ∃ tgt,
        Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
    exact
      Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.comm_exists_from_parComponents_src
        (src := src)
        (x := .fvar x)
        (body := Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P (n ++ "_L") v))
        (q := rhoDrop (.fvar z))
        hmemIn hmemOut
  -- Build the rfStepAt branch.
  exact
    EncodedSCStepSource.rfStepAt
      (P := Process.par (Process.input x y P) (Process.output x z))
      (Q := P.substitute y z)
      (n := n) (v := v)
      (h := ForwardSimulation.ReducesRF.comm x y z P)
      (hrf := hrfSrc)
      (hsafe := hsafe)
      (hsrcSC := Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)

/-- EncodedSC step-classifier for RF COMM redexes up to structural congruence:
produces the rfStepAt branch and a core COMM witness using component
inversion + `comm_exists_from_parComponents`. -/
theorem encodedSC_step_classifier_rf_comm_candidate_sc
    {N : Finset String} {src : Pattern}
    (x y z : Name) (P : Process) (n v : String)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe
      (ForwardSimulation.ReducesRF.comm x y z P))
    (hsc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode (Process.par (Process.input x y P) (Process.output x z)) n v)) :
    EncodedSCStepSource N src ∧
    ∃ tgt, Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
  have hclass :
      EncodedSCStepSource N src :=
    EncodedSCStepSource.rfStepAt
      (P := Process.par (Process.input x y P) (Process.output x z))
      (Q := P.substitute y z)
      (n := n) (v := v)
      (h := ForwardSimulation.ReducesRF.comm x y z P)
      (hrf := by
        simp [ForwardSimulation.RestrictionFree, hrf])
      (hsafe := hsafe)
      (hsrcSC := hsc)
  let src0 := encode (Process.par (Process.input x y P) (Process.output x z)) n v
  have hmemIn :
      .apply "PInput"
        [.fvar x,
          .lambda (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P (n ++ "_L") v))]
        ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src0 := by
    simp [src0, encode, rhoPar, rhoInput, rhoOutput, rhoDrop, piNameToRhoName,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents]
  have hmemOut :
      .apply "POutput" [.fvar x, rhoDrop (.fvar z)]
        ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents src0 := by
    simp [src0, encode, rhoPar, rhoInput, rhoOutput, rhoDrop, piNameToRhoName,
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents]
  have hcomm0 :
      ∃ tgt,
        Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src0 tgt) := by
    exact
      Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.comm_exists_from_parComponents_src
        (src := src0)
        (x := .fvar x)
        (body := Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P (n ++ "_L") v))
        (q := rhoDrop (.fvar z))
        hmemIn hmemOut
  rcases hcomm0 with ⟨tgt, hred⟩
  have hred' :
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
      hsc (Classical.choice hred)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)⟩
  exact ⟨hclass, ⟨tgt, hred'⟩⟩

/-- Fresh EncodedSC classifier for RF COMM redexes up to structural congruence. -/
theorem encodedSC_step_classifier_rf_comm_candidate_sc_fresh
    {N : Finset String} {src : Pattern}
    (x y z : Name) (P : Process) (n v : String)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe
      (ForwardSimulation.ReducesRF.comm x y z P))
    (hsc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode (Process.par (Process.input x y P) (Process.output x z)) n v))
    (hobs :
      N ⊆ (Process.par (Process.input x y P) (Process.output x z)).freeNames)
    (hfresh :
      EncodingFreshAt (Process.par (Process.input x y P) (Process.output x z)) n v) :
    EncodedSCStepSourceFresh N src ∧
    ∃ tgt, Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
  have hclass :
      EncodedSCStepSourceFresh N src :=
    EncodedSCStepSourceFresh.rfStepAt
      (P := Process.par (Process.input x y P) (Process.output x z))
      (Q := P.substitute y z)
      (n := n) (v := v)
      (h := ForwardSimulation.ReducesRF.comm x y z P)
      (hrf := by simp [ForwardSimulation.RestrictionFree, hrf])
      (hsafe := hsafe)
      (hsrcSC := hsc)
      (hobs := hobs)
      (hfresh := hfresh)
  have hcomm :
      ∃ tgt, Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) :=
    (encodedSC_step_classifier_rf_comm_candidate_sc
      (N := N) (src := src)
      (x := x) (y := y) (z := z) (P := P) (n := n) (v := v)
      hrf hsafe hsc).2
  exact ⟨hclass, hcomm⟩

/-- Generic RF one-step target-sensitive core extraction from an SC source. -/
theorem rfStepAt_oneStep_toCore
    {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (_hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) := by
  rcases hstep with ⟨hfirst⟩
  have hcanonEnc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
        (encode P n v) := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
    simpa using hasDerivedHead_encode_rf hrf n v
  have hcanonSrc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical src := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.coreCanonical_of_SC
        hcanonEnc
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsrcSC)
  exact
    ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerived.toCore_of_coreCanonical
      hcanonSrc hfirst⟩

/-- Generic RF one-step reflected right-branch data from an SC source. -/
theorem rfStepAt_oneStep_partition_right
    {N : Finset String} {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (_hstep : Nonempty (src ⇝ᵈ tgt)) :
    ∃ P' P'' n' v' tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
      Nonempty (P' ⇝ P'') ∧
      Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P'' n' v') := by
  have hpi : Nonempty (P ⇝ Q) := reducesRF_to_reduces h
  rcases ForwardSimulation.forward_single_step_rf h hrf hsafe n v with
    ⟨tgt', hstepCore, hscTgt⟩
  have hstepDerived :
      Nonempty ((encode P n v) ⇝ᵈ* tgt') := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived
      (Classical.choice hstepCore)⟩
  have hrfQ : ForwardSimulation.RestrictionFree Q :=
    ForwardSimulation.reducesRF_preserves_rf h hrf
  have hcanonEncodeQ :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
        (encode Q n v) := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
    simpa using hasDerivedHead_encode_rf hrfQ n v
  have hcanonTgt :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical tgt' := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.coreCanonical_of_SC
        hcanonEncodeQ
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hscTgt)
  have hbisim : tgt' ≈ᵈ{N} (encode Q n v) := by
    exact WeakRestrictedBisimD.of_SC_coreCanonical
      (N := N) (p := tgt') (q := encode Q n v) hscTgt hcanonTgt
  exact ⟨P, Q, n, v, tgt', hsrcSC, hpi, hstepDerived, hbisim⟩

/-! ## RF multi-step (trace) reflection endpoints -/

/-- Restriction-free preservation along RF multi-step traces. -/
theorem restrictionFree_of_multiStepRF
    {P Q : Process} (h : ForwardSimulation.MultiStepRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P) :
    ForwardSimulation.RestrictionFree Q := by
  induction h with
  | refl P =>
      simpa using hrf
  | step hstep hrest ih =>
      exact ih (ForwardSimulation.reducesRF_preserves_rf hstep hrf)

/-- Forward RF-trace endpoint (derived): multi-step RF traces produce a derived
trace and a derived bisim to the encoded target. -/
theorem rfTraceAt_forward
    {N : Finset String}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.MultiStepRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.MultiCommSafe h) :
    ∃ T, Nonempty ((encode P n v) ⇝ᵈ* T) ∧
      WeakRestrictedBisimD N T (encode Q n v) := by
  rcases ForwardSimulation.forward_multi_step_rf h hrf hsafe n v with
    ⟨T, hstar, hsc⟩
  have hderived :
      Nonempty ((encode P n v) ⇝ᵈ* T) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived
      (Classical.choice hstar)⟩
  have hrfQ : ForwardSimulation.RestrictionFree Q :=
    restrictionFree_of_multiStepRF h hrf
  have hcanonEncodeQ :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
        (encode Q n v) := by
    unfold Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical
    simpa using hasDerivedHead_encode_rf hrfQ n v
  have hcanonT :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.CoreCanonical T := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.coreCanonical_of_SC
        hcanonEncodeQ
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsc)
  have hbisim : WeakRestrictedBisimD N T (encode Q n v) := by
    exact WeakRestrictedBisimD.of_SC_coreCanonical (N := N) (p := T) (q := encode Q n v) hsc hcanonT
  exact ⟨T, hderived, hbisim⟩

/-- Encoded RF trace sources (multi-step): admin sources or exact RF-encoded
sources. -/
inductive EncodedRFTraceSource (N : Finset String) : Pattern → Prop where
  | admin {src : Pattern} :
      AdminSource src →
      EncodedRFTraceSource N src
  | rfTraceAt (P Q : Process) (n v : String)
      (h : ForwardSimulation.MultiStepRF P Q)
      (hrf : ForwardSimulation.RestrictionFree P)
      (hsafe : ForwardSimulation.MultiCommSafe h) :
      EncodedRFTraceSource N (encode P n v)

/-- Branch-sensitive RF trace reflection: admin-progress or RF-trace forward
endpoint, in a single statement. -/
theorem weak_backward_reflection_trace_encodedRF
    {N : Finset String} {src : Pattern}
    (hsrc : EncodedRFTraceSource N src) :
    (∃ tgt canon,
      Nonempty (src ⇝ᵈ* tgt) ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt canon)
    ∨
    (∃ P Q n v T,
      src = encode P n v ∧
      Nonempty (ForwardSimulation.MultiStepRF P Q) ∧
      Nonempty (src ⇝ᵈ* T) ∧
      WeakRestrictedBisimD N T (encode Q n v)) := by
  cases hsrc with
  | admin hAdmin =>
      rcases admin_source_forward_progress (N := N) hAdmin with
        ⟨tgt, canon, hstep, hcanon, hbisim⟩
      exact Or.inl ⟨tgt, canon, hstep, hcanon, hbisim⟩
  | rfTraceAt P Q n v h hrf hsafe =>
      rcases rfTraceAt_forward (N := N) P Q n v h hrf hsafe with
        ⟨T, hstep, hbisim⟩
      exact Or.inr ⟨P, Q, n, v, T, rfl, ⟨h⟩, hstep, hbisim⟩

/-! ## Generic RF one-step endpoint over SC sources -/
theorem weak_backward_reflection_step_rfStepAt_target_sensitive
    {N : Finset String} {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
    (∃ P' P'' n' v' tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
      Nonempty (P' ⇝ P'') ∧
      Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P'' n' v')) := by
  refine ⟨?_, ?_⟩
  · exact rfStepAt_oneStep_toCore
      (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC hstep
  · exact rfStepAt_oneStep_partition_right
      (N := N) (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC hstep

/-- Freshness + user-observation discipline for the RF one-step target-sensitive
endpoint: includes disjointness of the chosen seed pair `{n, v}`. -/
theorem weak_backward_reflection_step_rfStepAt_target_sensitive_fresh_userObs
    {N : Finset String} {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFreshAt P n v)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    Disjoint N ({ n, v } : Finset Name) ∧
    (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      (∃ P' P'' n' v' tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
        Nonempty (P' ⇝ P'') ∧
        Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P'' n' v'))) := by
  have hdisj : Disjoint N ({ n, v } : Finset Name) :=
    obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v) hobs hfresh
  have htarget :=
    weak_backward_reflection_step_rfStepAt_target_sensitive
      (N := N) (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v)
      h hrf hsafe hsrcSC hstep
  exact ⟨hdisj, htarget⟩

/-- Freshness + user-observation discipline for RF one-step sources:
bundles disjointness of the chosen seed pair with the backward `piStep` outcome. -/
theorem weak_backward_outcome_piStep_rfStepAt_fresh_userObs
    {N : Finset String} {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFreshAt P n v)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    WeakBackwardOutcomeFreshAt N src ({ n, v } : Finset Name) := by
  have hdisj : Disjoint N ({ n, v } : Finset Name) :=
    obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v) hobs hfresh
  rcases weak_backward_reflection_step_rfStepAt_target_sensitive
      (N := N) (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC hstep with
    ⟨_hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
  exact ⟨hdisj, WeakBackwardOutcome.piStep P' P'' n' v' tgt' hsrcSC' hpi hstar hbisim⟩

/-- Trace-sensitive target-sensitive decomposition for generic RF one-step SC
sources. -/
theorem weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive
    {N : Finset String} {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    src = tgt
    ∨
    (∃ mid,
      Nonempty (src ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
        ∃ P' P'' n' v' tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD N tgt' (encode P'' n' v'))) := by
  rcases hstep with ⟨hs⟩
  cases hs with
  | refl =>
      exact Or.inl rfl
  | step hfirst hrest =>
      rcases weak_backward_reflection_step_rfStepAt_target_sensitive
          (N := N) (src := src) (tgt := _)
          (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe hsrcSC ⟨hfirst⟩ with
        ⟨hcore, hright⟩
      exact Or.inr ⟨_, ⟨hfirst⟩, ⟨hrest⟩, hcore, hright⟩

/-- Freshness + user-observation discipline for the RF star-level
trace-sensitive target-sensitive endpoint: includes disjointness of `{n, v}`. -/
theorem weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive_fresh_userObs
    {N : Finset String} {src tgt : Pattern}
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFreshAt P n v)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    Disjoint N ({ n, v } : Finset Name) ∧
    (src = tgt
      ∨
      (∃ mid,
        Nonempty (src ⇝ᵈ mid) ∧
        Nonempty (mid ⇝ᵈ* tgt) ∧
        (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
          ∃ P' P'' n' v' tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
            Nonempty (P' ⇝ P'') ∧
            Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
            WeakRestrictedBisimD N tgt' (encode P'' n' v')))) := by
  have hdisj : Disjoint N ({ n, v } : Finset Name) :=
    obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v) hobs hfresh
  have htarget :=
    weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive
      (N := N) (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v)
      h hrf hsafe hsrcSC hstep
  exact ⟨hdisj, htarget⟩

/-- Observation-set weakening for generic RF one-step target-sensitive
backward endpoints over SC sources. -/
theorem weak_backward_reflection_step_rfStepAt_target_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
    (∃ P' P'' n' v' tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
      Nonempty (P' ⇝ P'') ∧
      Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P'' n' v')) := by
  rcases weak_backward_reflection_step_rfStepAt_target_sensitive
      (N := Nsup) (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v)
      h hrf hsafe hsrcSC hstep with
    ⟨hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
  exact ⟨hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, WeakRestrictedBisimD.mono hbisim hsub⟩

/-- Observation-set weakening for generic RF trace-sensitive target-sensitive
backward endpoints over SC sources. -/
theorem weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (P Q : Process) (n v : String)
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hsrcSC :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src
        (encode P n v))
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    src = tgt
    ∨
    (∃ mid,
      Nonempty (src ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
        ∃ P' P'' n' v' tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD N tgt' (encode P'' n' v'))) := by
  rcases weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive
      (N := Nsup) (src := src) (tgt := tgt)
      (P := P) (Q := Q) (n := n) (v := v)
      h hrf hsafe hsrcSC hstep with hrefl | hstepd
  · exact Or.inl hrefl
  · rcases hstepd with ⟨mid, hmid, hrest, hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
    exact Or.inr
      ⟨mid, hmid, hrest, hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar,
        WeakRestrictedBisimD.mono hbisim hsub⟩

/-- One-step reflection over the broader EncodedSC-driven classifier. -/
theorem weak_backward_reflection_oneStep_encodedSC
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    WeakBackwardOutcome N src := by
  rcases hstep with ⟨hfirst⟩
  cases EncodedSCStepSource.to_admin_or_rf hsrc with
  | inl hAdmin =>
      exact weak_backward_reflection_nonRF_admin (N := N) hAdmin
  | inr hrfData =>
      rcases hrfData with ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩
      rcases weak_backward_reflection_step_rfStepAt_target_sensitive
          (N := N) (src := src) (tgt := tgt)
          (P := P) (Q := Q) (n := n) (v := v)
          h hrf hsafe hsrcSC ⟨hfirst⟩ with
        ⟨_hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
      exact WeakBackwardOutcome.piStep P' P'' n' v' tgt' hsrcSC' hpi hstar hbisim

/-- Constructor-sensitive one-step reflection over `EncodedSCStepSource`:
for admin sources, returns explicit admin-progress branch data with an
`AdminSource` witness; for RF-step sources, returns target-sensitive
reflected π-step branch data. -/
theorem weak_backward_reflection_step_encodedSC_branch_sensitive
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      ∃ P' P'' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
        Nonempty (P' ⇝ P'') ∧
        Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P'' n v)) := by
  cases EncodedSCStepSource.to_admin_or_rf hsrc with
  | inl hAdmin =>
      rcases admin_source_forward_progress (N := N) hAdmin with
        ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inl ⟨tgt', canon, hstar, hcanon, hbisim⟩
  | inr hrfData =>
      rcases hrfData with ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩
      exact Or.inr <| weak_backward_reflection_step_rfStepAt_target_sensitive
        (N := N) (src := src) (tgt := tgt)
        (P := P) (Q := Q) (n := n) (v := v)
        h hrf hsafe hsrcSC hstep

/-- Branch-sensitive one-step reflection for RF COMM redexes up to SC:
builds the EncodedSC classifier using component inversion + `comm_exists_from_parComponents`,
then applies the generic branch-sensitive step reflection. -/
theorem weak_backward_reflection_step_comm_candidate_sc_branch_sensitive
    {N : Finset String} {src tgt : Pattern}
    (x y z : Name) (P : Process) (n v : String)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe
      (ForwardSimulation.ReducesRF.comm x y z P))
    (hsc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode (Process.par (Process.input x y P) (Process.output x z)) n v))
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      ∃ P' P'' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
        Nonempty (P' ⇝ P'') ∧
        Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P'' n v)) := by
  have hclass :
      EncodedSCStepSource N src :=
    (encodedSC_step_classifier_rf_comm_candidate_sc
      (N := N) (src := src)
      (x := x) (y := y) (z := z) (P := P) (n := n) (v := v)
      hrf hsafe hsc).1
  exact weak_backward_reflection_step_encodedSC_branch_sensitive
    (N := N) (src := src) (tgt := tgt) hclass hstep

/-- Constructor-sensitive trace decomposition over `EncodedSCStepSource`:
for admin sources, returns explicit admin-progress branch data with an
`AdminSource` witness; for RF-step sources, consumes the full star
witness and returns the trace-sensitive + target-sensitive reflected branch
decomposition. -/
theorem weak_backward_reflection_star_encodedSC_branch_sensitive
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (src = tgt
      ∨
      (∃ mid,
        Nonempty (src ⇝ᵈ mid) ∧
        Nonempty (mid ⇝ᵈ* tgt) ∧
        (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
          ∃ P' P'' n v tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
            Nonempty (P' ⇝ P'') ∧
            Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
            WeakRestrictedBisimD N tgt' (encode P'' n v)))) := by
  cases EncodedSCStepSource.to_admin_or_rf hsrc with
  | inl hAdmin =>
      rcases admin_source_forward_progress (N := N) hAdmin with
        ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inl ⟨tgt', canon, hstar, hcanon, hbisim⟩
  | inr hrfData =>
      rcases hrfData with ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩
      exact Or.inr <|
        weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive
        (N := N) (src := src) (tgt := tgt)
        (P := P) (Q := Q) (n := n) (v := v)
        h hrf hsafe hsrcSC hstep

/-- Constructor-sensitive one-step reflection over the fresh EncodedSC
classifier, with explicit disjointness of the relevant seed set. -/
theorem weak_backward_reflection_step_encodedSC_branch_sensitive_fresh_userObs
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSourceFresh N src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ seeds tgt' canon,
      Disjoint N seeds ∧
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ n v,
      Disjoint N ({ n, v } : Finset Name) ∧
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
        ∃ P' P'' n' v' tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD N tgt' (encode P'' n' v'))) := by
  cases hsrc with
  | admin hAdmin =>
      rcases admin_source_forward_progress_fresh (N := N) (src := src) hAdmin with
        ⟨seeds, tgt', canon, hdisj, hstep', hcanon, hbisim⟩
      exact Or.inl ⟨seeds, tgt', canon, hdisj, hstep', hcanon, hbisim⟩
  | rfStepAt P Q n v h hrf hsafe hsrcSC hobs hfresh =>
      have hdisj : Disjoint N ({ n, v } : Finset Name) :=
        obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v)
          hobs hfresh
      rcases weak_backward_reflection_step_rfStepAt_target_sensitive
          (N := N) (src := src) (tgt := tgt)
          (P := P) (Q := Q) (n := n) (v := v)
          h hrf hsafe hsrcSC hstep with
        ⟨hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
      exact Or.inr ⟨n, v, hdisj, hcore, P', P'', n', v', tgt',
        hsrcSC', hpi, hstar, hbisim⟩

/-- Fresh backward outcome from a fresh EncodedSC step source: packages the
branch-sensitive result into a `WeakBackwardOutcomeFreshAt` witness. -/
theorem weak_backward_outcome_fresh_of_encodedSC_step_source_fresh
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSourceFresh N src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    ∃ seeds, WeakBackwardOutcomeFreshAt N src seeds := by
  rcases
      weak_backward_reflection_step_encodedSC_branch_sensitive_fresh_userObs
        (N := N) (src := src) (tgt := tgt) hsrc hstep with
    hadmin | hrf
  · rcases hadmin with ⟨seeds, tgt', canon, hdisj, hstep', hcanon, hbisim⟩
    exact ⟨seeds, hdisj,
      WeakBackwardOutcome.adminProgress tgt' canon hstep' hcanon hbisim⟩
  · rcases hrf with
      ⟨n, v, hdisj, _hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
    exact ⟨({ n, v } : Finset Name), hdisj,
      WeakBackwardOutcome.piStep P' P'' n' v' tgt' hsrcSC' hpi hstar hbisim⟩

/-- Fresh branch-sensitive one-step reflection for RF COMM redexes up to SC:
builds the fresh EncodedSC classifier, then applies the fresh branch-sensitive
step reflection. -/
theorem weak_backward_reflection_step_comm_candidate_sc_branch_sensitive_fresh_userObs
    {N : Finset String} {src tgt : Pattern}
    (x y z : Name) (P : Process) (n v : String)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe
      (ForwardSimulation.ReducesRF.comm x y z P))
    (hsc :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        src (encode (Process.par (Process.input x y P) (Process.output x z)) n v))
    (hobs :
      N ⊆ (Process.par (Process.input x y P) (Process.output x z)).freeNames)
    (hfresh :
      EncodingFreshAt (Process.par (Process.input x y P) (Process.output x z)) n v)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ seeds tgt' canon,
      Disjoint N seeds ∧
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ n v,
      Disjoint N ({ n, v } : Finset Name) ∧
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
        ∃ P' P'' n' v' tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD N tgt' (encode P'' n' v'))) := by
  have hclass :
      EncodedSCStepSourceFresh N src :=
    (encodedSC_step_classifier_rf_comm_candidate_sc_fresh
      (N := N) (src := src)
      (x := x) (y := y) (z := z) (P := P) (n := n) (v := v)
      hrf hsafe hsc hobs hfresh).1
  exact weak_backward_reflection_step_encodedSC_branch_sensitive_fresh_userObs
    (N := N) (src := src) (tgt := tgt) hclass hstep

/-- Constructor-sensitive star-level reflection over the fresh EncodedSC
classifier, with explicit disjointness of the relevant seed set. -/
theorem weak_backward_reflection_star_encodedSC_branch_sensitive_fresh_userObs
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSourceFresh N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    (∃ seeds tgt' canon,
      Disjoint N seeds ∧
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ n v,
      Disjoint N ({ n, v } : Finset Name) ∧
      (src = tgt
        ∨
        (∃ mid,
          Nonempty (src ⇝ᵈ mid) ∧
          Nonempty (mid ⇝ᵈ* tgt) ∧
          (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
            ∃ P' P'' n' v' tgt',
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
              Nonempty (P' ⇝ P'') ∧
              Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
              WeakRestrictedBisimD N tgt' (encode P'' n' v'))))) := by
  cases hsrc with
  | admin hAdmin =>
      rcases admin_source_forward_progress_fresh (N := N) (src := src) hAdmin with
        ⟨seeds, tgt', canon, hdisj, hstep', hcanon, hbisim⟩
      exact Or.inl ⟨seeds, tgt', canon, hdisj, hstep', hcanon, hbisim⟩
  | rfStepAt P Q n v h hrf hsafe hsrcSC hobs hfresh =>
      have hdisj : Disjoint N ({ n, v } : Finset Name) :=
        obs_disjoint_seedPair_of_subset_freeNames (P := P) (N := N) (n := n) (v := v)
          hobs hfresh
      rcases weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive
          (N := N) (src := src) (tgt := tgt)
          (P := P) (Q := Q) (n := n) (v := v)
          h hrf hsafe hsrcSC hstep with hrefl | hstepd
      · exact Or.inr ⟨n, v, hdisj, Or.inl hrefl⟩
      · rcases hstepd with ⟨mid, hmid, hrest, hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
        exact Or.inr ⟨n, v, hdisj, Or.inr
          ⟨mid, hmid, hrest, hcore, P', P'', n', v', tgt',
            hsrcSC', hpi, hstar, hbisim⟩⟩

/-- Fresh backward outcome from a fresh EncodedSC star source: packages the
trace-sensitive fresh branch data into a `WeakBackwardOutcomeFreshAt` witness. -/
theorem weak_backward_outcome_fresh_of_encodedSC_star_source_fresh
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSourceFresh N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    ∃ seeds, WeakBackwardOutcomeFreshAt N src seeds := by
  cases hsrc with
  | admin hAdmin =>
      rcases admin_source_forward_progress_fresh (N := N) (src := src) hAdmin with
        ⟨seeds, tgt', canon, hdisj, hstep', hcanon, hbisim⟩
      exact ⟨seeds, hdisj,
        WeakBackwardOutcome.adminProgress tgt' canon hstep' hcanon hbisim⟩
  | rfStepAt P Q n v h hrf hsafe hsrcSC hobs hfresh =>
      rcases weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive_fresh_userObs
          (N := N) (src := src) (tgt := tgt)
          (P := P) (Q := Q) (n := n) (v := v)
          h hrf hsafe hsrcSC hobs hfresh hstep with
        ⟨hdisj, hrefl | hstepd⟩
      · have hout : WeakBackwardOutcome N src :=
          weak_backward_outcome_piStep_rf_step_of_SC_source_at
            (N := N) (P := P) (Q := Q) h hrf hsafe n v hsrcSC
        exact ⟨({ n, v } : Finset Name), hdisj, hout⟩
      · rcases hstepd with
          ⟨mid, hmid, hrest, _hcore, P', P'', n', v', tgt', hsrcSC', hpi, hstar, hbisim⟩
        exact ⟨({ n, v } : Finset Name), hdisj,
          WeakBackwardOutcome.piStep P' P'' n' v' tgt' hsrcSC' hpi hstar hbisim⟩

/-- Observation-set weakening for constructor-sensitive one-step EncodedSC
decomposition endpoints. -/
theorem weak_backward_reflection_step_encodedSC_branch_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      ∃ P' P'' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
        Nonempty (P' ⇝ P'') ∧
        Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P'' n v)) := by
  rcases weak_backward_reflection_step_encodedSC_branch_sensitive
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep with hleft | hright
  · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
    exact Or.inl ⟨tgt', canon, hstar, hcanon, WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hright with ⟨hcore, P', P'', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
    exact Or.inr ⟨hcore, P', P'', n, v, tgt', hsrcSC, hpi, hstar, WeakRestrictedBisimD.mono hbisim hsub⟩

/-- Observation-set weakening for constructor-sensitive star EncodedSC
decomposition endpoints. -/
theorem weak_backward_reflection_star_encodedSC_branch_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (src = tgt
      ∨
      (∃ mid,
        Nonempty (src ⇝ᵈ mid) ∧
        Nonempty (mid ⇝ᵈ* tgt) ∧
        (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
          ∃ P' P'' n v tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
            Nonempty (P' ⇝ P'') ∧
            Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
            WeakRestrictedBisimD N tgt' (encode P'' n v)))) := by
  rcases weak_backward_reflection_star_encodedSC_branch_sensitive
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep with hleft | hright
  · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
    exact Or.inl ⟨tgt', canon, hstar, hcanon, WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hright with hrefl | hstepd
    · exact Or.inr (Or.inl hrefl)
    · rcases hstepd with ⟨mid, hmid, hrest, hcore, P', P'', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
      exact Or.inr (Or.inr
        ⟨mid, hmid, hrest, hcore, P', P'', n, v, tgt', hsrcSC, hpi, hstar,
          WeakRestrictedBisimD.mono hbisim hsub⟩)

/-- Star-indexed `WeakBackwardOutcome` endpoint derived from constructor-sensitive
branch data. This consumes the full `⇝ᵈ*` witness through
`weak_backward_reflection_star_encodedSC_branch_sensitive`. -/
theorem weak_backward_reflection_star_encodedSC_from_branch_sensitive
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    WeakBackwardOutcome N src := by
  rcases weak_backward_reflection_star_encodedSC_branch_sensitive
      (N := N) (src := src) (tgt := tgt) hsrc hstep with hleft | hright
  · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
    exact WeakBackwardOutcome.adminProgress tgt' canon hstar hcanon hbisim
  · rcases hright with hrefl | hstepd
    · cases EncodedSCStepSource.to_admin_or_rf hsrc with
      | inl hAdmin =>
          exact weak_backward_reflection_nonRF_admin (N := N) hAdmin
      | inr hrfData =>
          rcases hrfData with ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩
          exact weak_backward_outcome_piStep_rf_step_of_SC_source_at
            (N := N) (P := P) (Q := Q) h hrf hsafe n v hsrcSC
    · rcases hstepd with ⟨_mid, _hmid, _hrest, _hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
      exact WeakBackwardOutcome.piStep P P' n v tgt' hsrcSC hpi hstar hbisim

/-- Observation-set weakening for the star-indexed branch-sensitive outcome
endpoint. -/
theorem weak_backward_reflection_star_encodedSC_from_branch_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    WeakBackwardOutcome N src := by
  have houtSup :
      WeakBackwardOutcome Nsup src :=
    weak_backward_reflection_star_encodedSC_from_branch_sensitive
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep
  exact WeakBackwardOutcome.mono houtSup hsub

/-- One-step partition theorem over the broader EncodedSC step-source family:
from a witnessed derived one-step, obtain explicit branch data for either
administrative progress or reflected π-step correspondence. -/
theorem weak_backward_reflection_step_encodedSC_partition
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ P P' n v tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
      Nonempty (P ⇝ P') ∧
      Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  cases EncodedSCStepSource.to_admin_or_rf hsrc with
  | inl hAdmin =>
      rcases admin_source_forward_progress (N := N) hAdmin with
        ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inl ⟨tgt', canon, hstar, hcanon, hbisim⟩
  | inr hrfData =>
      rcases hrfData with ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩
      have htarget :
          Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
          (∃ P' P'' n' v' tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n' v') ∧
            Nonempty (P' ⇝ P'') ∧
            Nonempty ((encode P' n' v') ⇝ᵈ* tgt') ∧
            WeakRestrictedBisimD N tgt' (encode P'' n' v')) :=
        weak_backward_reflection_step_rfStepAt_target_sensitive
          (N := N) (src := src) (tgt := tgt)
          (P := P) (Q := Q) (n := n) (v := v)
          h hrf hsafe hsrcSC hstep
      exact Or.inr <| htarget.2

/-- Observation-set weakening for one-step EncodedSC partition endpoints:
if the partition holds at a superset of observed channels, it also holds at any
subset by monotonicity of `WeakRestrictedBisimD`. -/
theorem weak_backward_reflection_step_encodedSC_partition_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ P P' n v tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
      Nonempty (P ⇝ P') ∧
      Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  rcases weak_backward_reflection_step_encodedSC_partition
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep with hpart | hpart
  · rcases hpart with ⟨tgt', canon, hstar, hcanon, hbisim⟩
    exact Or.inl ⟨tgt', canon, hstar, hcanon, WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hpart with ⟨P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
    exact Or.inr ⟨P, P', n, v, tgt', hsrcSC, hpi, hstar, WeakRestrictedBisimD.mono hbisim hsub⟩

/-- Target-sensitive one-step partition over EncodedSC step-sources:
admin sources produce admin-progress branch; RF-step sources additionally
provide a core one-step witness to the concrete target. -/
theorem weak_backward_reflection_step_encodedSC_partition_target_sensitive
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      ∃ P P' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
        Nonempty (P ⇝ P') ∧
        Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  cases EncodedSCStepSource.to_admin_or_rf hsrc with
  | inl hAdmin =>
      rcases admin_source_forward_progress (N := N) hAdmin with
        ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inl ⟨tgt', canon, hstar, hcanon, hbisim⟩
  | inr hrfData =>
      rcases hrfData with ⟨P, Q, n, v, h, hrf, hsafe, hsrcSC⟩
      rcases weak_backward_reflection_step_rfStepAt_target_sensitive
          (N := N) (src := src) (tgt := tgt)
          (P := P) (Q := Q) (n := n) (v := v)
          h hrf hsafe hsrcSC hstep with
        ⟨hcore, hright⟩
      exact Or.inr ⟨hcore, hright⟩

/-- Observation-set weakening for target-sensitive one-step EncodedSC partition
endpoints. -/
theorem weak_backward_reflection_step_encodedSC_partition_target_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      ∃ P P' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
        Nonempty (P ⇝ P') ∧
        Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  rcases weak_backward_reflection_step_encodedSC_partition_target_sensitive
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep with hleft | hright
  · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
    exact Or.inl ⟨tgt', canon, hstar, hcanon, WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hright with ⟨hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
    exact Or.inr ⟨hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, WeakRestrictedBisimD.mono hbisim hsub⟩

/-- Star-level partition theorem over EncodedSC step-sources:
consumes a full derived trace witness and returns explicit branch data. -/
theorem weak_backward_reflection_star_encodedSC_partition
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ P P' n v tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
      Nonempty (P ⇝ P') ∧
      Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  rcases hstep with ⟨hs⟩
  cases hs with
  | refl =>
      have hout :
          WeakBackwardOutcome N src :=
        weak_backward_reflection_star_encodedSC_from_branch_sensitive
          (N := N) (src := src) (tgt := src) hsrc ⟨.refl src⟩
      cases hout with
      | adminProgress tgt' canon hstar hcanon hbisim =>
          exact Or.inl ⟨tgt', canon, hstar, hcanon, hbisim⟩
      | piStep P P' n v tgt' hsrcSC hpi hstar hbisim =>
          exact Or.inr ⟨P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
  | step hfirst _hrest =>
      exact weak_backward_reflection_step_encodedSC_partition
        (N := N) (src := src) (tgt := _) hsrc ⟨hfirst⟩

/-- Trace-sensitive star decomposition over EncodedSC step-sources:
consumes the full `⇝ᵈ*` witness and either identifies the reflexive case
(`src = tgt`) or extracts a concrete head step plus tail trace. The head step
is then partitioned into admin-progress or reflected π-step data. -/
theorem weak_backward_reflection_star_encodedSC_partition_trace_sensitive
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    src = tgt
    ∨
    (∃ mid,
      Nonempty (src ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      ((∃ tgt' canon,
        Nonempty (src ⇝ᵈ* tgt') ∧
        AdminCanonicalTarget src canon ∧
        WeakRestrictedBisimD N tgt' canon)
      ∨
      (∃ P P' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
        Nonempty (P ⇝ P') ∧
        Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P' n v)))) := by
  rcases hstep with ⟨hs⟩
  cases hs with
  | refl =>
      exact Or.inl rfl
  | step hfirst hrest =>
      have hpart :
          (∃ tgt' canon,
            Nonempty (src ⇝ᵈ* tgt') ∧
            AdminCanonicalTarget src canon ∧
            WeakRestrictedBisimD N tgt' canon)
          ∨
          (∃ P P' n v tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
            Nonempty (P ⇝ P') ∧
            Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
            WeakRestrictedBisimD N tgt' (encode P' n v)) :=
        weak_backward_reflection_step_encodedSC_partition
          (N := N) (src := src) (tgt := _) hsrc ⟨hfirst⟩
      exact Or.inr ⟨_, ⟨hfirst⟩, ⟨hrest⟩, by simpa using hpart⟩

/-- Trace-sensitive + target-sensitive star decomposition over EncodedSC
step-sources: on non-refl traces, exposes head/tail decomposition and keeps
the reflected branch target-sensitive at the concrete head-step target. -/
theorem weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    src = tgt
    ∨
    (∃ mid,
      Nonempty (src ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      ((∃ tgt' canon,
        Nonempty (src ⇝ᵈ* tgt') ∧
        AdminCanonicalTarget src canon ∧
        WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
        ∃ P P' n v tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
          Nonempty (P ⇝ P') ∧
          Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD N tgt' (encode P' n v)))) := by
  rcases hstep with ⟨hs⟩
  cases hs with
  | refl =>
      exact Or.inl rfl
  | step hfirst hrest =>
      have hpart :
          (∃ tgt' canon,
            Nonempty (src ⇝ᵈ* tgt') ∧
            AdminCanonicalTarget src canon ∧
            WeakRestrictedBisimD N tgt' canon)
          ∨
          (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src _) ∧
            ∃ P P' n v tgt',
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
              Nonempty (P ⇝ P') ∧
              Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
              WeakRestrictedBisimD N tgt' (encode P' n v)) :=
        weak_backward_reflection_step_encodedSC_partition_target_sensitive
          (N := N) (src := src) (tgt := _) hsrc ⟨hfirst⟩
      exact Or.inr ⟨_, ⟨hfirst⟩, ⟨hrest⟩, by simpa using hpart⟩

/-- Fully general backward-simulation endpoint over EncodedSC step-sources.
It flattens the trace-sensitive decomposition into three branches:
refl, admin-progress, or reflected π-step data with explicit head/tail trace. -/
theorem weak_backward_full_simulation_encodedSC
    {N : Finset String} {src tgt : Pattern}
    (hsrc : EncodedSCStepSource N src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    src = tgt
    ∨
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ mid,
      Nonempty (src ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
      ∃ P P' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
        Nonempty (P ⇝ P') ∧
        Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  rcases weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive
      (N := N) (src := src) (tgt := tgt) hsrc hstep with hrefl | htail
  · exact Or.inl hrefl
  · rcases htail with ⟨mid, hmid, hrest, hbranch⟩
    rcases hbranch with hadmin | hpi
    · rcases hadmin with ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inr (Or.inl ⟨tgt', canon, hstar, hcanon, hbisim⟩)
    · rcases hpi with ⟨hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
      exact Or.inr (Or.inr
        ⟨mid, hmid, hrest, hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩)

/-- Encoded-source specialization of the full backward-simulation endpoint:
requires an `EncodedSCStepSource` classifier witness for `encode P n v`. -/
theorem weak_backward_full_simulation_encode
    {N : Finset String} {P : Process} {n v : String} {tgt : Pattern}
    (hsrc : EncodedSCStepSource N (encode P n v))
    (hstep : Nonempty ((encode P n v) ⇝ᵈ* tgt)) :
    encode P n v = tgt
    ∨
    (∃ tgt' canon,
      Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget (encode P n v) canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ mid,
      Nonempty ((encode P n v) ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces (encode P n v) mid) ∧
      ∃ P0 P1 n0 v0 tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
          (encode P n v) (encode P0 n0 v0) ∧
        Nonempty (P0 ⇝ P1) ∧
        Nonempty ((encode P0 n0 v0) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P1 n0 v0)) := by
  exact weak_backward_full_simulation_encodedSC
    (N := N) (src := encode P n v) (tgt := tgt) hsrc hstep

/-- RF-step-at encoded-source specialization:
builds the `EncodedSCStepSource` classifier from a concrete RF witness and
instantiates `weak_backward_full_simulation_encode`. -/
theorem weak_backward_full_simulation_encode_rfStepAt
    {N : Finset String} {P Q : Process} {n v : String} {tgt : Pattern}
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (hstep : Nonempty ((encode P n v) ⇝ᵈ* tgt)) :
    encode P n v = tgt
    ∨
    (∃ tgt' canon,
      Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget (encode P n v) canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ mid,
      Nonempty ((encode P n v) ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces (encode P n v) mid) ∧
      ∃ P0 P1 n0 v0 tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
          (encode P n v) (encode P0 n0 v0) ∧
        Nonempty (P0 ⇝ P1) ∧
        Nonempty ((encode P0 n0 v0) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD N tgt' (encode P1 n0 v0)) := by
  exact weak_backward_full_simulation_encode
    (N := N) (P := P) (n := n) (v := v) (tgt := tgt)
    (hsrc := EncodedSCStepSource.rfStepAt
      (P := P) (Q := Q) (n := n) (v := v) h hrf hsafe
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _))
    hstep

/-- Observation-set weakening for trace-sensitive+target-sensitive star
decomposition over EncodedSC step-sources. -/
theorem weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    src = tgt
    ∨
    (∃ mid,
      Nonempty (src ⇝ᵈ mid) ∧
      Nonempty (mid ⇝ᵈ* tgt) ∧
      ((∃ tgt' canon,
        Nonempty (src ⇝ᵈ* tgt') ∧
        AdminCanonicalTarget src canon ∧
        WeakRestrictedBisimD N tgt' canon)
      ∨
      (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
        ∃ P P' n v tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
          Nonempty (P ⇝ P') ∧
          Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD N tgt' (encode P' n v)))) := by
  rcases weak_backward_reflection_star_encodedSC_partition_trace_sensitive_target_sensitive
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep with hrefl | hstepd
  · exact Or.inl hrefl
  · rcases hstepd with ⟨mid, hmid, hrest, hpart⟩
    rcases hpart with hleft | hright
    · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
      exact Or.inr ⟨mid, hmid, hrest, Or.inl
        ⟨tgt', canon, hstar, hcanon, WeakRestrictedBisimD.mono hbisim hsub⟩⟩
    · rcases hright with ⟨hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
      exact Or.inr ⟨mid, hmid, hrest, Or.inr
        ⟨hcore, P, P', n, v, tgt', hsrcSC, hpi, hstar, WeakRestrictedBisimD.mono hbisim hsub⟩⟩

/-- Observation-set weakening for star-level EncodedSC partition endpoints. -/
theorem weak_backward_reflection_star_encodedSC_partition_of_obsSuperset
    {N Nsup : Finset String} {src tgt : Pattern}
    (hsub : N ⊆ Nsup)
    (hsrc : EncodedSCStepSource Nsup src)
    (hstep : Nonempty (src ⇝ᵈ* tgt)) :
    (∃ tgt' canon,
      Nonempty (src ⇝ᵈ* tgt') ∧
      AdminCanonicalTarget src canon ∧
      WeakRestrictedBisimD N tgt' canon)
    ∨
    (∃ P P' n v tgt',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P n v) ∧
      Nonempty (P ⇝ P') ∧
      Nonempty ((encode P n v) ⇝ᵈ* tgt') ∧
      WeakRestrictedBisimD N tgt' (encode P' n v)) := by
  rcases weak_backward_reflection_star_encodedSC_partition
      (N := Nsup) (src := src) (tgt := tgt) hsrc hstep with hleft | hright
  · rcases hleft with ⟨tgt', canon, hstar, hcanon, hbisim⟩
    exact Or.inl ⟨tgt', canon, hstar, hcanon, WeakRestrictedBisimD.mono hbisim hsub⟩
  · rcases hright with ⟨P, P', n, v, tgt', hsrcSC, hpi, hstar, hbisim⟩
    exact Or.inr ⟨P, P', n, v, tgt', hsrcSC, hpi, hstar, WeakRestrictedBisimD.mono hbisim hsub⟩

/-- Non-empty-observation canary for the adminProgress branch. -/
theorem weak_backward_reflection_nonRF_admin_canary_nonempty :
    WeakBackwardOutcome ({ "v_init" } : Finset String)
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])) := by
  simpa using
    (weak_backward_reflection_nonRF_admin
      (N := ({ "v_init" } : Finset String))
      (AdminSource.nuListener "x" .nil "n_init" "v_init" rhoNil))

/-- Non-empty-observation canary for the seed-listener adminProgress branch. -/
theorem weak_backward_reflection_nonRF_admin_seed_canary_nonempty :
    WeakBackwardOutcome ({ "ns_z" } : Finset String)
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) := by
  simpa using
    (weak_backward_reflection_nonRF_admin
      (N := ({ "ns_z" } : Finset String))
      (AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" rhoNil))

/-- Observation-set weakening for the non-empty ν-listener admin canary. -/
theorem weak_backward_reflection_nonRF_admin_nu_canary_nonempty_of_obsSuperset
    {N Nsup : Finset String} (hsub : N ⊆ Nsup) :
    WeakBackwardOutcome Nsup
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])) →
    WeakBackwardOutcome N
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])) := by
  intro h
  exact WeakBackwardOutcome.mono h hsub

/-- Regression: strict-superset weakening check for ν-listener admin branch.
If the outcome holds at `{v_init, aux}`, it also holds at `{v_init}`. -/
theorem weak_backward_reflection_nonRF_admin_nu_obs_superset_regression :
    WeakBackwardOutcome ({ "v_init", "aux" } : Finset String)
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])) →
    WeakBackwardOutcome ({ "v_init" } : Finset String)
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])) := by
  intro h
  exact weak_backward_reflection_nonRF_admin_nu_canary_nonempty_of_obsSuperset
    (N := ({ "v_init" } : Finset String))
    (Nsup := ({ "v_init", "aux" } : Finset String))
    (hsub := by
      intro x hx
      simp at hx ⊢
      exact Or.inl hx)
    h

/-- Observation-set weakening for the non-empty seed-listener admin canary. -/
theorem weak_backward_reflection_nonRF_admin_seed_canary_nonempty_of_obsSuperset
    {N Nsup : Finset String} (hsub : N ⊆ Nsup) :
    WeakBackwardOutcome Nsup
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) →
    WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) := by
  intro h
  exact WeakBackwardOutcome.mono h hsub

/-- Regression: strict-superset weakening check for seed-listener admin branch.
If the outcome holds at `{ns_z, aux}`, it also holds at `{ns_z}`. -/
theorem weak_backward_reflection_nonRF_admin_seed_obs_superset_regression :
    WeakBackwardOutcome ({ "ns_z", "aux" } : Finset String)
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) →
    WeakBackwardOutcome ({ "ns_z" } : Finset String)
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil])) := by
  intro h
  exact weak_backward_reflection_nonRF_admin_seed_canary_nonempty_of_obsSuperset
    (N := ({ "ns_z" } : Finset String))
    (Nsup := ({ "ns_z", "aux" } : Finset String))
    (hsub := by
      intro x hx
      simp at hx ⊢
      exact Or.inl hx)
    h

/-- Non-empty observation canary for the generic RF-step SC-source `piStep`
wrapper. -/
theorem weak_backward_outcome_piStep_rf_step_of_SC_source_at_canary_nonempty :
    WeakBackwardOutcome ({ "alpha" } : Finset String)
      (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
        "n_custom" "v_custom") := by
  let Psrc : Process := Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w")
  let Qdst : Process := .nil
  have hrfSrc : ForwardSimulation.RestrictionFree Psrc := by
    simp [Psrc, ForwardSimulation.RestrictionFree]
  have hsafe :
      ForwardSimulation.CommSafe (ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil) := by
    change "u" ≠ "w" ∧ ForwardSimulation.BarendregtFor "u" "w" .nil
    exact ⟨by decide, by simp [ForwardSimulation.BarendregtFor]⟩
  exact
    weak_backward_outcome_piStep_rf_step_of_SC_source_at
      (N := ({ "alpha" } : Finset String))
      (P := Psrc) (Q := Qdst)
      (h := ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil)
      hrfSrc hsafe "n_custom" "v_custom"
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)

/-- Non-empty canary for the generic RF-step one-step target-sensitive
backward endpoint. -/
theorem weak_backward_reflection_step_rfStepAt_target_sensitive_canary_nonempty :
    ∃ tgt,
      Nonempty
        ((encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
          "n_custom" "v_custom") ⇝ᵈ tgt) ∧
      (Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
          (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
            "n_custom" "v_custom")
          tgt) ∧
        ∃ P' P'' n v tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
            (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
              "n_custom" "v_custom")
            (encode P' n v) ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD ({ "alpha" } : Finset String) tgt' (encode P'' n v)) := by
  let Psrc : Process := Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w")
  let src : Pattern := encode Psrc "n_custom" "v_custom"
  let Qdst : Process := .nil
  have hrfSrc : ForwardSimulation.RestrictionFree Psrc := by
    simp [Psrc, ForwardSimulation.RestrictionFree]
  have hsafe :
      ForwardSimulation.CommSafe (ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil) := by
    change "u" ≠ "w" ∧ ForwardSimulation.BarendregtFor "u" "w" .nil
    exact ⟨by decide, by simp [ForwardSimulation.BarendregtFor]⟩
  have hcore :
      ∃ tgt, Nonempty (src ⇝ tgt) := by
    simpa [src, Psrc, encode, rhoPar, rhoInput, rhoOutput, rhoDrop, piNameToRhoName] using
      (Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.comm_exists_from_encoded_source_via_canInteract
          "alpha" "u" "w" .nil ("n_custom" ++ "_L") "v_custom" [])
  rcases hcore with ⟨tgt, hcoreStep⟩
  have hstepD : Nonempty (src ⇝ᵈ tgt) := ⟨.core (Classical.choice hcoreStep)⟩
  have htarget :
      Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src tgt) ∧
      (∃ P' P'' n v tgt',
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
        Nonempty (P' ⇝ P'') ∧
        Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
        WeakRestrictedBisimD ({ "alpha" } : Finset String) tgt' (encode P'' n v)) :=
    weak_backward_reflection_step_rfStepAt_target_sensitive
      (N := ({ "alpha" } : Finset String))
      (src := src) (tgt := tgt)
      (P := Psrc) (Q := Qdst) (n := "n_custom") (v := "v_custom")
      (h := ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil)
      hrfSrc hsafe
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
      hstepD
  exact ⟨tgt, hstepD, htarget⟩

/-- Non-empty observation canary for the generic RF-step star-level
trace-sensitive target-sensitive backward endpoint. -/
theorem weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive_canary_nonempty :
    (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
        "n_custom" "v_custom") =
      (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
        "n_custom" "v_custom")
    ∨
    (∃ mid,
      Nonempty
        ((encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
          "n_custom" "v_custom") ⇝ᵈ mid) ∧
      Nonempty
        (mid ⇝ᵈ*
          (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
            "n_custom" "v_custom")) ∧
      (Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
          (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
            "n_custom" "v_custom")
          mid) ∧
        ∃ P' P'' n v tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
            (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
              "n_custom" "v_custom")
            (encode P' n v) ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD ({ "alpha" } : Finset String) tgt' (encode P'' n v))) := by
  let Psrc : Process := Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w")
  let src : Pattern := encode Psrc "n_custom" "v_custom"
  let Qdst : Process := .nil
  have hrfSrc : ForwardSimulation.RestrictionFree Psrc := by
    simp [Psrc, ForwardSimulation.RestrictionFree]
  have hsafe :
      ForwardSimulation.CommSafe (ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil) := by
    change "u" ≠ "w" ∧ ForwardSimulation.BarendregtFor "u" "w" .nil
    exact ⟨by decide, by simp [ForwardSimulation.BarendregtFor]⟩
  have hstep : Nonempty (src ⇝ᵈ* src) := ⟨.refl src⟩
  have h :=
    weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive
      (N := ({ "alpha" } : Finset String)) (src := src) (tgt := src)
      (P := Psrc) (Q := Qdst) (n := "n_custom") (v := "v_custom")
      (h := ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil)
      hrfSrc hsafe
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
      hstep
  dsimp [src] at h
  exact h

/-- Observation-set weakening regression for the generic RF-step star-level
trace-sensitive target-sensitive endpoint. -/
theorem weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive_canary_nonempty_of_obsSuperset :
    (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
        "n_custom" "v_custom") =
      (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
        "n_custom" "v_custom")
    ∨
    (∃ mid,
      Nonempty
        ((encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
          "n_custom" "v_custom") ⇝ᵈ mid) ∧
      Nonempty
        (mid ⇝ᵈ*
          (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
            "n_custom" "v_custom")) ∧
      (Nonempty
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
          (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
            "n_custom" "v_custom")
          mid) ∧
        ∃ P' P'' n v tgt',
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
            (encode (Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w"))
              "n_custom" "v_custom")
            (encode P' n v) ∧
          Nonempty (P' ⇝ P'') ∧
          Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
          WeakRestrictedBisimD ({ "alpha" } : Finset String) tgt' (encode P'' n v))) := by
  let Psrc : Process := Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w")
  let src : Pattern := encode Psrc "n_custom" "v_custom"
  let Qdst : Process := .nil
  have hrfSrc : ForwardSimulation.RestrictionFree Psrc := by
    simp [Psrc, ForwardSimulation.RestrictionFree]
  have hsafe :
      ForwardSimulation.CommSafe (ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil) := by
    change "u" ≠ "w" ∧ ForwardSimulation.BarendregtFor "u" "w" .nil
    exact ⟨by decide, by simp [ForwardSimulation.BarendregtFor]⟩
  have hstep : Nonempty (src ⇝ᵈ* src) := ⟨.refl src⟩
  have hsup :
      src = src
      ∨
      (∃ mid,
        Nonempty (src ⇝ᵈ mid) ∧
        Nonempty (mid ⇝ᵈ* src) ∧
        (Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces src mid) ∧
          ∃ P' P'' n v tgt',
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src (encode P' n v) ∧
            Nonempty (P' ⇝ P'') ∧
            Nonempty ((encode P' n v) ⇝ᵈ* tgt') ∧
            WeakRestrictedBisimD ({ "alpha" } : Finset String) tgt' (encode P'' n v))) :=
    (weak_backward_reflection_star_rfStepAt_trace_sensitive_target_sensitive_of_obsSuperset
      (N := ({ "alpha" } : Finset String))
      (Nsup := ({ "alpha", "aux" } : Finset String))
      (src := src) (tgt := src)
      (hsub := by
        intro x hx
        simp at hx ⊢
        exact Or.inl hx)
      (P := Psrc) (Q := Qdst) (n := "n_custom") (v := "v_custom")
      (h := ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil)
      hrfSrc hsafe
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
      hstep)
  dsimp [src] at hsup
  exact hsup


/-- Non-empty observation canary for the fresh star-level outcome wrapper
over rfStepAt sources. -/
theorem weak_backward_outcome_fresh_of_encodedSC_star_source_fresh_canary_nonempty :
    ∃ seeds,
      WeakBackwardOutcomeFreshAt ({ "alpha" } : Finset String)
        (encode (Process.par (Process.input "alpha" "u" .nil)
          (Process.output "alpha" "w")) "n_custom" "v_custom") seeds := by
  let Psrc : Process :=
    Process.par (Process.input "alpha" "u" .nil) (Process.output "alpha" "w")
  let src : Pattern := encode Psrc "n_custom" "v_custom"
  have hrfSrc : ForwardSimulation.RestrictionFree Psrc := by
    simp [Psrc, ForwardSimulation.RestrictionFree]
  have hsafe :
      ForwardSimulation.CommSafe (ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil) := by
    change "u" ≠ "w" ∧ ForwardSimulation.BarendregtFor "u" "w" .nil
    exact ⟨by decide, by simp [ForwardSimulation.BarendregtFor]⟩
  have hobs :
      ({ "alpha" } : Finset String) ⊆ Psrc.freeNames := by
    simp [Psrc, Process.freeNames]
  have hfresh : EncodingFreshAt Psrc "n_custom" "v_custom" := by
    simp [EncodingFreshAt, Psrc, Process.freeNames]
    decide
  have hsrc :
      EncodedSCStepSourceFresh ({ "alpha" } : Finset String) src :=
    encodedSC_step_classifier_rfStepAt_fresh
      (N := ({ "alpha" } : Finset String))
      (src := src)
      (P := Psrc) (Q := .nil) (n := "n_custom") (v := "v_custom")
      (h := ForwardSimulation.ReducesRF.comm "alpha" "u" "w" .nil)
      hrfSrc hsafe
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
      hobs hfresh
  have hstep : Nonempty (src ⇝ᵈ* src) := ⟨.refl src⟩
  simpa [src] using
    (weak_backward_outcome_fresh_of_encodedSC_star_source_fresh
      (N := ({ "alpha" } : Finset String)) (src := src) (tgt := src) hsrc hstep)

/-- Regression: combined admin + piStep weakening in one statement.
If both outcomes hold at strict supersets, they hold at the reduced sets. -/
theorem weak_backward_outcome_admin_and_piStep_obs_superset_regression
    (hnu : WeakBackwardOutcome ({ "v_init", "aux" } : Finset String)
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])))
    (hcomm : WeakBackwardOutcome ({ "a", "aux" } : Finset String)
      (encode (Process.par (Process.input "a" "y" .nil) (Process.output "a" "z"))
        "n_init" "v_init")) :
    WeakBackwardOutcome ({ "v_init" } : Finset String)
      (rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil])) ∧
    WeakBackwardOutcome ({ "a" } : Finset String)
      (encode (Process.par (Process.input "a" "y" .nil) (Process.output "a" "z"))
        "n_init" "v_init") := by
  refine ⟨?_, ?_⟩
  · exact weak_backward_reflection_nonRF_admin_nu_canary_nonempty_of_obsSuperset
      (N := ({ "v_init" } : Finset String))
      (Nsup := ({ "v_init", "aux" } : Finset String))
      (hsub := by
        intro x hx
        simp at hx ⊢
        exact Or.inl hx)
      hnu
  · exact WeakBackwardOutcome.mono
      hcomm
      (by
        intro x hx
        simp at hx ⊢
        exact Or.inl hx)

/-- Full non-RF admin correspondence (both directions, derived weak form):
forward wrappers plus backward reflection outcomes for ν/seed/replicate admin sources. -/
theorem full_nonRF_admin_correspondence_bidir {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String) :
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) := by
  rcases full_nonRF_forward_correspondence_derived
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v with
    ⟨hrepFwd, hnuFwd⟩
  have hbackNu :
      WeakBackwardOutcome N
        (rhoPar (encode (.nu x P) "n_init" "v_init")
          (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]))
      (AdminSource.nuListener x P "n_init" "v_init" nuListenerBody)
  have hbackSeed :
      WeakBackwardOutcome N
        (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
          (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]))
      (AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" seedListenerBody)
  have hbackRep :
      WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := encode (.replicate xr yr Pr) n v)
      (AdminSource.replicate xr yr Pr n v)
  exact ⟨hrepFwd, hnuFwd, hbackNu, hbackSeed, hbackRep⟩

/-- Freshness-threaded variant of the full non-RF admin bidirectional package. -/
theorem full_nonRF_admin_correspondence_bidir_fresh {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hfresh : EncodingFresh P) :
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) := by
  rcases full_nonRF_forward_correspondence_derived_fresh
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh with
    ⟨hrepFwd, hnuFwd⟩
  have hbackNu :
      WeakBackwardOutcome N
        (rhoPar (encode (.nu x P) "n_init" "v_init")
          (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]))
      (AdminSource.nuListener x P "n_init" "v_init" nuListenerBody)
  have hbackSeed :
      WeakBackwardOutcome N
        (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
          (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]))
      (AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" seedListenerBody)
  have hbackRep :
      WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := encode (.replicate xr yr Pr) n v)
      (AdminSource.replicate xr yr Pr n v)
  exact ⟨hrepFwd, hnuFwd, hbackNu, hbackSeed, hbackRep⟩

/-- Freshness plus user-observation discipline yields explicit non-interference
of reserved full-encode names alongside the backward/admin outcomes. -/
theorem full_nonRF_admin_correspondence_bidir_fresh_userObs {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : EncodingFresh P) :
    Disjoint N fullEncodeReservedNames ∧
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) := by
  have hdisj : Disjoint N fullEncodeReservedNames :=
    obs_disjoint_reserved_of_subset_freeNames (P := P) (N := N) hobs hfresh
  have hrest :=
    full_nonRF_admin_correspondence_bidir_fresh
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
  exact ⟨hdisj, hrest⟩

/-- Backward reflection package for the combined non-RF administrative closure:
extracts explicit source components and encoded-image witnesses. -/
theorem backward_reflect_fullEncode_nu_admin_progress {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern) :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      srcNu = rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      EncodedSC "n_init" "v_init" (encode (.nu x P) "n_init" "v_init") ∧
      EncodedSC "n_init" "v_init" srcRep ∧
      Nonempty
        ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (.collection .hashBag [Tnu, Tseed] none)
        (.collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N Trep
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")) := by
  let srcNu : Pattern := rhoPar (encode (.nu x P) "n_init" "v_init")
    (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])
  let srcSeed : Pattern := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
    (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])
  let srcRep : Pattern := encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"
  rcases fullEncode_nu_admin_progress_combined_derived
      (N := N) x P nuListenerBody seedListenerBody with
    ⟨Tnu, Tseed, Trep, hfull, htrace, hswap, hnu, hseed, hrep⟩
  refine ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hfull, rfl, rfl, rfl, ?_, ?_, htrace, hswap, hnu, hseed, hrep⟩
  · exact encode_is_EncodedSC (.nu x P) "n_init" "v_init"
  · simpa [srcRep] using
      (encode_is_EncodedSC (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")

/-- Concrete backward-stage canary. -/
theorem backward_reflect_fullEncode_nu_admin_progress_canary :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      srcNu = rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      Nonempty ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, Trep] none)) := by
  rcases backward_reflect_fullEncode_nu_admin_progress
      (N := (∅ : Finset String)) "x" .nil rhoNil rhoNil with
    ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hfull, hnuEq, hseedEq, hrepEq, _hEncNu, _hEncRep, htrace, _hswap, _hnu, _hseed, _hrep⟩
  exact ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hfull, hnuEq, hseedEq, hrepEq, htrace⟩

/-- Nontrivial backward-stage canary with concrete non-`rhoNil` listeners. -/
theorem backward_reflect_fullEncode_nu_admin_progress_canary_nontrivial :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      srcNu = rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda (.apply "PDrop" [.fvar "k"])]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda (.apply "NQuote" [.fvar "m"])]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      Nonempty ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, Trep] none)) := by
  rcases backward_reflect_fullEncode_nu_admin_progress
      (N := (∅ : Finset String)) "x" .nil
      (.apply "PDrop" [.fvar "k"]) (.apply "NQuote" [.fvar "m"]) with
    ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, _hfull, hnuEq, hseedEq, hrepEq,
      _hEncNu, _hEncRep, htrace, _hswap, _hnu, _hseed, _hrep⟩
  exact ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hnuEq, hseedEq, hrepEq, htrace⟩

/-- Strong nontrivial backward-stage canary:
concrete listeners with encoded-image witnesses and endpoint bisim outputs. -/
theorem backward_reflect_fullEncode_nu_admin_progress_canary_nontrivial_full :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      srcNu = rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda (.apply "PDrop" [.fvar "k"])]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda (.apply "NQuote" [.fvar "m"])]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      EncodedSC "n_init" "v_init" (encode (.nu "x" .nil) "n_init" "v_init") ∧
      EncodedSC "n_init" "v_init" srcRep ∧
      Nonempty ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (.collection .hashBag [Tnu, Tseed] none)
        (.collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (.apply "PDrop" [.fvar "k"]) (.fvar "n_init"),
           rhoInput (.fvar "n_init") "x" (encode .nil ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (.apply "NQuote" [.fvar "m"]) (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Trep
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")) := by
  simpa using
    (backward_reflect_fullEncode_nu_admin_progress
      (N := (∅ : Finset String)) "x" .nil
      (.apply "PDrop" [.fvar "k"]) (.apply "NQuote" [.fvar "m"]))

end Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection
