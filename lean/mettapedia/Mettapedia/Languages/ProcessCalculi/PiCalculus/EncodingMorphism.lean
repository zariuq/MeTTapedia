import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisim
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimDerived
import Mettapedia.Languages.ProcessCalculi.PiCalculus.NameServerLemmas
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# Encoding Morphism: π → ρ (Forward Direction)

Organizes the Lybech (2022) encoding correctness proof as a structured
morphism, following the LanguageMorphism framework.

## What Is Fully Proved

1. **The encoding function** (`encode : Process → String → String → Pattern`)
   in `RhoEncoding.lean`.

2. **The Encoded grammar** (`Encoded n v P`) — a syntactic characterization of
   the image of `encode`, with a proven `encode_is_Encoded` theorem.

3. **The OSLF framework** (`LanguageMorphism`, `piCalc : LanguageDef`,
   `forward_multi_strong`, `preserves_diamond`) — generic simulation theory.

4. **Bisimilarity infrastructure** (`WeakRestrictedBisim` with refl/symm/trans/
   mono/of_SC/empty, `RhoBisimilar` with refl/symm/trans) — all proven.

## Forward Direction (RF)

The forward simulation (`prop4_forward`) is exposed for the restriction-free
fragment using:
- `forward_single_step` (RF single-step)
- `forward_multi_step` (RF multi-step)

## Backward Direction

Backward reflection is developed separately in
`PiCalculus/BackwardAdminReflection.lean`, including:
- Encoded-image inversion lemmas
- SC-normalized COMM decomposition via `parComponents`/`canInteract`
- Branch-sensitive one-step and star-level reflection outcomes

## References

- Lybech (2022), Section 6, pages 104-107
- Gorla (2010), "Towards a Unified Approach to Encodability and Separation Results"
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
open Mettapedia.OSLF.Framework.LangMorphism

/-! ## The "Encoded" Predicate

Describes the grammar of patterns that `encode P n v` can produce for any
Process P. This constrains the image of the encoding and is the foundation
for any future backward-direction work.

Key property: `encode_is_Encoded` (proven) shows every encoded process
satisfies this grammar. -/

/-- Patterns in the image of the encoding function `encode P n v`.

    Each constructor mirrors one case of `encode`:
    - `nil`: encode(.nil) = rhoNil (empty bag)
    - `par`: encode(P|Q) = rhoPar(encode P n_L v)(encode Q n_R v)
    - `input`: encode(x(y).P) = rhoInput(.fvar x, y, encode P)
    - `output`: encode(x<z>) = rhoOutput(.fvar x, rhoDrop(.fvar z))
    - `nu`: encode(νx.P) = rhoPar(v<n>)(n(x).encode P ns v)
    - `replicate`: encode(!x(y).P) = rhoReplicate(rhoInput(.fvar x, y, encode P)) -/
inductive Encoded : String → String → Pattern → Prop where
  | nil (n v : String) : Encoded n v rhoNil
  | par {n v : String} {P Q : Pattern} :
      Encoded (n ++ "_L") v P → Encoded (n ++ "_R") v Q →
      Encoded n v (rhoPar P Q)
  | input {n v : String} {x y : String} {body : Pattern} :
      Encoded n v body →
      Encoded n v (rhoInput (.fvar x) y body)
  | output {n v : String} (x z : String) :
      Encoded n v (rhoOutput (.fvar x) (rhoDrop (.fvar z)))
  | nu {n v : String} {x : String} {body : Pattern} :
      Encoded (n ++ "_" ++ n) v body →
      Encoded n v (rhoPar (rhoOutput (.fvar v) (.fvar n))
                          (rhoInput (.fvar n) x body))
  | replicate {n v : String} {x y : String} {body : Pattern} :
      Encoded (n ++ "_rep") v body →
      Encoded n v (rhoReplicate (rhoInput (.fvar x) y body))

/-- The encoding function produces Encoded patterns. -/
theorem encode_is_Encoded (P : Process) (n v : String) :
    Encoded n v (encode P n v) := by
  induction P generalizing n with
  | nil => exact .nil n v
  | par P Q ihP ihQ => exact .par (ihP (n ++ "_L")) (ihQ (n ++ "_R"))
  | input x y P ihP => exact .input (ihP n)
  | output x z => exact .output x z
  | nu x P ihP => exact .nu (ihP (n ++ "_" ++ n))
  | replicate x y P ihP => exact .replicate (ihP (n ++ "_rep"))

private theorem rhoPar_ne_apply (P Q : Pattern) (f : String) (args : List Pattern) :
    rhoPar P Q ≠ .apply f args := by
  intro hEq
  cases P <;> cases Q <;>
    simp only [rhoPar] at hEq <;>
    first
    | exact Pattern.noConfusion hEq
    | (split at hEq <;> exact Pattern.noConfusion hEq)

private theorem apply_tag_ne (f g : String) (hf : f ≠ g) (as bs : List Pattern) :
    (.apply f as : Pattern) ≠ .apply g bs := by
  intro hEq
  have htag : f = g := by
    simpa using congrArg (fun p =>
      match p with
      | .apply tag _ => tag
      | _ => "") hEq
  exact hf htag

private theorem rhoPar_eq_parComponents_append (p q : Pattern) :
    rhoPar p q = .collection .hashBag
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents p ++
       Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents q) none := by
  cases p <;> cases q <;>
    simp only [rhoPar, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] <;>
    (repeat (first | cases ‹CollType› | cases ‹Option String›)) <;>
    first | rfl | (split <;> first | rfl | simp_all)

/-- Inversion on encoded top-level inputs:
if the encoded image has a `PInput` head, it is exactly an input-encoding form. -/
theorem encoded_input_forms {n v : String} {p ch body : Pattern}
    (h : Encoded n v p)
    (hp : p = .apply "PInput" [ch, .lambda none body]) :
    ∃ x y p,
      ch = .fvar x ∧
      body = Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y p ∧
      Encoded n v p := by
  cases h with
  | nil _ _ =>
      exact False.elim ((by simp [rhoNil] : rhoNil ≠ .apply "PInput" [ch, .lambda none body]) hp)
  | @par _ _ P Q _ _ =>
      exact False.elim ((rhoPar_ne_apply P Q "PInput" [ch, .lambda none body]) hp)
  | @input _ _ x y bodyIn hbody =>
      refine ⟨x, y, bodyIn, ?_, ?_, hbody⟩
      · cases hp
        rfl
      · cases hp
        rfl
  | output x z =>
      exact False.elim
        ((apply_tag_ne "POutput" "PInput" (by decide)
          [.fvar x, rhoDrop (.fvar z)] [ch, .lambda none body]) hp)
  | @nu _ _ x bodyNu _ =>
      exact False.elim
        ((rhoPar_ne_apply (rhoOutput (.fvar v) (.fvar n)) (rhoInput (.fvar n) x bodyNu)
          "PInput" [ch, .lambda none body]) hp)
  | @replicate _ _ x y bodyRep _ =>
      exact False.elim
        ((apply_tag_ne "PReplicate" "PInput" (by decide)
          [rhoInput (.fvar x) y bodyRep] [ch, .lambda none body]) hp)

/-- RF membership inversion for encoded inputs:
if a `PInput` component appears in the parallel components of an RF encoding,
it must be an encoded input with an RF body. -/
theorem encode_rf_parComponents_input
    {P : Process} (hrf : ForwardSimulation.RestrictionFree P)
    {n v : String} {ch body : Pattern}
    (hmem :
      .apply "PInput" [ch, .lambda none body] ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
          (encode P n v)) :
    ∃ x y P' n',
      ch = .fvar x ∧
      body = Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P' n' v) ∧
      ForwardSimulation.RestrictionFree P' := by
  induction P generalizing n with
  | nil =>
      simp [encode, rhoNil, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents]
        at hmem
  | par P Q ihP ihQ =>
      have hmem' :
          .apply "PInput" [ch, .lambda none body] ∈
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
                (encode P (n ++ "_L") v) ++
             Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
                (encode Q (n ++ "_R") v)) := by
        simpa [encode, rhoPar_eq_parComponents_append,
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] using hmem
      rcases List.mem_append.mp hmem' with hmemL | hmemR
      · rcases ihP hrf.1 hmemL with ⟨x, y, P', n', hch, hbody, hrf'⟩
        exact ⟨x, y, P', n', hch, hbody, hrf'⟩
      · rcases ihQ hrf.2 hmemR with ⟨x, y, P', n', hch, hbody, hrf'⟩
        exact ⟨x, y, P', n', hch, hbody, hrf'⟩
  | input x y P ih =>
      have hmem' :
          .apply "PInput" [ch, .lambda none body] =
            rhoInput (.fvar x) y (encode P n v) := by
        simpa [encode, rhoInput,
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] using hmem
      have hch : ch = .fvar x := by
        simpa [rhoInput] using congrArg (fun p =>
          match p with
          | .apply _ [a, _] => a
          | _ => .bvar 0) hmem'
      have hbody :
          body = Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v) := by
        simpa [rhoInput] using congrArg (fun p =>
          match p with
          | .apply _ [_, .lambda _ b] => b
          | _ => .bvar 0) hmem'
      exact ⟨x, y, P, n, hch, hbody, hrf⟩
  | output x z =>
      simp [encode, rhoOutput,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at hmem
  | nu x P =>
      exact (False.elim (hrf))
  | replicate x y P =>
      exact (False.elim (hrf))

/-- Inversion on encoded top-level outputs:
if the encoded image has a `POutput` head, it is exactly an output-encoding form. -/
theorem encoded_output_forms {n v : String} {p ch payload : Pattern}
    (h : Encoded n v p)
    (hp : p = .apply "POutput" [ch, payload]) :
    ∃ x z, ch = .fvar x ∧ payload = rhoDrop (.fvar z) := by
  cases h with
  | nil _ _ =>
      exact False.elim ((by simp [rhoNil] : rhoNil ≠ .apply "POutput" [ch, payload]) hp)
  | @par _ _ P Q _ _ =>
      exact False.elim ((rhoPar_ne_apply P Q "POutput" [ch, payload]) hp)
  | @input _ _ x y bodyIn _ =>
      exact False.elim
        ((apply_tag_ne "PInput" "POutput" (by decide)
          [.fvar x, .lambda none (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y bodyIn)]
          [ch, payload]) hp)
  | output x z =>
      cases hp
      exact ⟨x, z, rfl, rfl⟩
  | @nu _ _ x bodyNu _ =>
      exact False.elim
        ((rhoPar_ne_apply (rhoOutput (.fvar v) (.fvar n)) (rhoInput (.fvar n) x bodyNu)
          "POutput" [ch, payload]) hp)
  | @replicate _ _ x y bodyRep _ =>
      exact False.elim
        ((apply_tag_ne "PReplicate" "POutput" (by decide)
          [rhoInput (.fvar x) y bodyRep] [ch, payload]) hp)

/-- RF membership inversion for encoded outputs:
if a `POutput` component appears in the parallel components of an RF encoding,
it must be an encoded output on some channel and drop payload. -/
theorem encode_rf_parComponents_output
    {P : Process} (hrf : ForwardSimulation.RestrictionFree P)
    {n v : String} {ch payload : Pattern}
    (hmem :
      .apply "POutput" [ch, payload] ∈
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
          (encode P n v)) :
    ∃ x z,
      ch = .fvar x ∧ payload = rhoDrop (.fvar z) := by
  induction P generalizing n with
  | nil =>
      simp [encode, rhoNil, Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents]
        at hmem
  | par P Q ihP ihQ =>
      have hmem' :
          .apply "POutput" [ch, payload] ∈
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
                (encode P (n ++ "_L") v) ++
             Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
                (encode Q (n ++ "_R") v)) := by
        simpa [encode, rhoPar_eq_parComponents_append,
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] using hmem
      rcases List.mem_append.mp hmem' with hmemL | hmemR
      · exact ihP hrf.1 hmemL
      · exact ihQ hrf.2 hmemR
  | input x y P ih =>
      simp [encode, rhoInput,
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] at hmem
  | output x z =>
      have hmem' :
          .apply "POutput" [ch, payload] =
            rhoOutput (.fvar x) (rhoDrop (.fvar z)) := by
        simpa [encode, rhoOutput,
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents] using hmem
      have hch : ch = .fvar x := by
        simpa [rhoOutput] using congrArg (fun p =>
          match p with
          | .apply _ [a, _] => a
          | _ => .bvar 0) hmem'
      have hpayload : payload = rhoDrop (.fvar z) := by
        simpa [rhoOutput] using congrArg (fun p =>
          match p with
          | .apply _ [_, b] => b
          | _ => .bvar 0) hmem'
      exact ⟨x, z, hch, hpayload⟩
  | nu x P =>
      exact (False.elim (hrf))
  | replicate x y P =>
      exact (False.elim (hrf))

/-! ## Forward Direction

Wraps existing proven infrastructure to state the forward simulation theorem:
if P ⇝ᵣ* P' in the RF π-fragment, then encode(P) →* T in the ρ-calculus
where T is weakly bisimilar to encode(P'). -/

/-- Forward simulation for one RF π-step, using WeakRestrictedBisim.

    Lifts from `forward_single_step` (SC conclusion) to bisim (weaker). -/
theorem forward_single_step_bisim {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.ReducesRF P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) := by
  obtain ⟨T, h_star, h_sc⟩ := forward_single_step h hrf hsafe n v
  exact ⟨T, h_star, WeakRestrictedBisim.of_SC h_sc⟩

/-- Multi-step RF forward simulation, using WeakRestrictedBisim.

    Lifts from `forward_multi_step` (SC conclusion) to bisim. -/
theorem forward_multi_step_bisim {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepRF P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.MultiCommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) := by
  obtain ⟨T, h_star, h_sc⟩ := forward_multi_step h hrf hsafe n v
  exact ⟨T, h_star, WeakRestrictedBisim.of_SC h_sc⟩

/-! ## Main Theorem: Forward Operational Correspondence (Prop 4, Forward)

The π→ρ encoding gives forward operational correspondence up to weak
bisimilarity. This is the MAIN theorem. -/

/-- Proposition 4 (Forward, RF fragment): π multi-step → ρ multi-step + bisim.

    If P ⇝ᵣ* P' in the RF π-fragment, then encode(P) →* T in the ρ-calculus
    where T is weakly bisimilar to encode(P').
 -/
theorem prop4_forward {N : Finset String} {P P' : Process}
    (h : ForwardSimulation.MultiStepRF P P')
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.MultiCommSafe h)
    (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) :=
  forward_multi_step_bisim h hrf hsafe n v

/-- Non-RF forward case for replication in the derived ρ layer.

This gives the first operational step for the `.replicate` encoding without
going through the RF restriction.
-/
theorem forward_replicate_case_derived {N : Finset String}
    (x y : Name) (P : Process) (n v : String) :
    ∃ T, Nonempty ((encode (.replicate x y P) n v) ⇝ᵈ* T) ∧
      T ≈{N}
        (rhoPar
          (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))
          (encode (.replicate x y P) n v)) := by
  let body : Pattern := rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v)
  let tgt : Pattern := .collection .hashBag [body, .apply "PReplicate" [body]] none
  refine ⟨tgt, ?_, ?_⟩
  · refine ⟨?_⟩
    simpa [body, tgt, encode, rhoReplicate] using
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.rep_unfold_single body)
  · simpa [body, tgt, encode, rhoPar, rhoReplicate] using
      (WeakRestrictedBisim.refl N tgt)

/-- Non-RF single-step forward case for `.replicate`, measured in derived weak bisimilarity. -/
theorem forward_single_step_replicate_derived {N : Finset String}
    (x y : Name) (P : Process) (n v : String) :
    ∃ T, Nonempty ((encode (.replicate x y P) n v) ⇝ᵈ* T) ∧
      T ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))
          (encode (.replicate x y P) n v)) := by
  let body : Pattern := rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v)
  let tgt : Pattern := .collection .hashBag [body, .apply "PReplicate" [body]] none
  refine ⟨tgt, ?_, ?_⟩
  · refine ⟨?_⟩
    simpa [body, tgt, encode, rhoReplicate] using
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.rep_unfold_single body)
  · simpa [body, tgt, encode, rhoPar, rhoReplicate] using
      (WeakRestrictedBisimD.refl N tgt)

/-- Non-RF single-step administrative progress for a name-server listener,
measured in derived weak bisimilarity. -/
theorem forward_single_step_nameServer_listener_derived {N : Finset String}
    (x z v s : String) (body : Pattern) :
    ∃ T, Nonempty ((rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda none body])) ⇝ᵈ* T) ∧
      T ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst body (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none) := by
  let tgt : Pattern := .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst body (.apply "PDrop" [.fvar s]),
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] none
  refine ⟨tgt, ?_, ?_⟩
  · simpa [tgt] using
      (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServer_request_response_progress_general
        x z v s body)
  · simpa [tgt] using (WeakRestrictedBisimD.refl N tgt)

/-- Seed-freshness-threaded wrapper for name-server listener progress.
The hypothesis is explicit API contract for downstream non-interference layers. -/
theorem forward_single_step_nameServer_listener_derived_fresh {N : Finset String}
    (x z v s : String) (body : Pattern)
    (_hfresh : EncodingFreshAt .nil z v) :
    ∃ T, Nonempty ((rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda none body])) ⇝ᵈ* T) ∧
      T ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst body (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none) := by
  exact forward_single_step_nameServer_listener_derived (N := N) x z v s body

/-- Independent administrative traces (ν-listener and seed-listener) commute
up to bag permutation on their combined targets. -/
private theorem commute_nu_seed_admin_steps_under_bag_perm
    {nuSrc nuTgt seedSrc seedTgt : Pattern}
    (hnu : nuSrc ⇝ᵈ* nuTgt) (hseed : seedSrc ⇝ᵈ* seedTgt) :
    Nonempty
      ((.collection .hashBag [nuSrc, seedSrc] none) ⇝ᵈ*
        (.collection .hashBag [nuTgt, seedTgt] none)) ∧
    (.collection .hashBag [nuTgt, seedTgt] none ≡
      .collection .hashBag [seedTgt, nuTgt] none) := by
  let hnuLift :
      (.collection .hashBag [nuSrc, seedSrc] none) ⇝ᵈ*
        (.collection .hashBag [nuTgt, seedSrc] none) :=
    ReducesDerivedStar.par_any (before := ([] : List Pattern)) (after := [seedSrc]) hnu
  let hseedLift :
      (.collection .hashBag [nuTgt, seedSrc] none) ⇝ᵈ*
        (.collection .hashBag [nuTgt, seedTgt] none) :=
    ReducesDerivedStar.par_any (before := [nuTgt]) (after := ([] : List Pattern)) hseed
  have htrace :
      (.collection .hashBag [nuSrc, seedSrc] none) ⇝ᵈ*
        (.collection .hashBag [nuTgt, seedTgt] none) :=
    ReducesDerivedStar.trans hnuLift hseedLift
  refine ⟨⟨htrace⟩, ?_⟩
  exact
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm
      [nuTgt, seedTgt] [seedTgt, nuTgt]
      (by simpa using (List.Perm.swap nuTgt seedTgt ([] : List Pattern)).symm)

/-- Non-RF single-step administrative progress for the `ν` encoding request,
consumed by a listener on channel `v` (derived weak bisim form). -/
theorem forward_single_step_nu_listener_derived {N : Finset String}
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    ∃ T, Nonempty ((rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda none listenerBody])) ⇝ᵈ* T) ∧
      T ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none) := by
  let outReq : Pattern := rhoOutput (.fvar v) (.fvar n)
  let bodyIn : Pattern := rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)
  let listener : Pattern := .apply "PInput" [.fvar v, .lambda none listenerBody]
  let src : Pattern := rhoPar (encode (.nu x P) n v) listener
  let preComm : Pattern := .collection .hashBag [outReq, listener, bodyIn] none
  let tgt : Pattern := .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n), bodyIn] none
  have hdecomp :=
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nu_listener_comm_decompose
      x P n v listenerBody
  have hpre : src ≡ preComm := by
    exact (by simpa
      [src, preComm, listener, outReq, bodyIn,
       Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nuListenerSource,
       Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nuListenerPreComm]
      using hdecomp.1)
  have hcomm : preComm ⇝ tgt := by
    exact (by simpa
      [tgt, bodyIn,
       Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nuListenerTarget]
      using (Classical.choice hdecomp.2))
  have hcore : src ⇝ tgt := by
    exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
      hpre hcomm (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
  refine ⟨tgt, ?_, ?_⟩
  · exact ⟨ReducesDerivedStar.single (.core hcore)⟩
  · simpa [tgt] using (WeakRestrictedBisimD.refl N tgt)

/-- Seed-freshness-threaded wrapper for ν-listener administrative progress. -/
theorem forward_single_step_nu_listener_derived_fresh {N : Finset String}
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern)
    (_hfresh : EncodingFreshAt P n v) :
    ∃ T, Nonempty ((rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda none listenerBody])) ⇝ᵈ* T) ∧
      T ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none) := by
  exact forward_single_step_nu_listener_derived (N := N) x P n v listenerBody

/-- Fixed-string canary for ν-listener administrative progress. -/
theorem forward_single_step_nu_listener_derived_canary :
    ∃ T, Nonempty
      ((rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda none rhoNil])) ⇝ᵈ* T) ∧
      T ≈ᵈ{∅}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.fvar "n_init"),
           rhoInput (.fvar "n_init") "x" (encode .nil ("n_init" ++ "_" ++ "n_init") "v_init")] none) := by
  simpa using
    (forward_single_step_nu_listener_derived
      (N := (∅ : Finset String)) "x" .nil "n_init" "v_init" rhoNil)

/-- Packaged non-RF administrative progress around `fullEncode (.nu x P)`
at canonical channels, assembled from the three non-RF endpoint theorems. -/
theorem fullEncode_nu_admin_progress_derived {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern) :
    fullEncode (.nu x P) =
      rhoPar (encode (.nu x P) "n_init" "v_init")
        (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
    (∃ Tnu, Nonempty
      ((rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda none nuListenerBody])) ⇝ᵈ* Tnu) ∧
      Tnu ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none)) ∧
    (∃ Tseed, Nonempty
      ((rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda none seedListenerBody])) ⇝ᵈ* Tseed) ∧
      Tseed ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none)) ∧
    (∃ Trep, Nonempty
      ((encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init") ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using
      (forward_single_step_nu_listener_derived
        (N := N) x P "n_init" "v_init" nuListenerBody)
  · simpa using
      (forward_single_step_nameServer_listener_derived
        (N := N) "ns_x" "ns_z" "v_init" "ns_seed" seedListenerBody)
  · simpa using
      (forward_single_step_replicate_derived
        (N := N) "ns_x" "_drop" .nil "n_init" "v_init")

/-- Freshness-threaded wrapper for packaged non-RF administrative ν progress. -/
theorem fullEncode_nu_admin_progress_derived_fresh {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern)
    (_hfresh : EncodingFresh P) :
    fullEncode (.nu x P) =
      rhoPar (encode (.nu x P) "n_init" "v_init")
        (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
    (∃ Tnu, Nonempty
      ((rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda none nuListenerBody])) ⇝ᵈ* Tnu) ∧
      Tnu ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none)) ∧
    (∃ Tseed, Nonempty
      ((rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda none seedListenerBody])) ⇝ᵈ* Tseed) ∧
      Tseed ≈ᵈ{N}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none)) ∧
    (∃ Trep, Nonempty
      ((encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init") ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) := by
  exact fullEncode_nu_admin_progress_derived
    (N := N) x P nuListenerBody seedListenerBody

/-- Combined non-RF administrative closure:
ν-listener, seed-listener, and replicate-unfold endpoints composed into one
derived multi-step trace over a single 3-component source bag. -/
theorem fullEncode_nu_admin_progress_combined_derived {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern) :
    ∃ Tnu Tseed Trep,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda none nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda none seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
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
      WeakRestrictedBisimD N Trep
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")) := by
  obtain ⟨Tnu, hnuStep, hnuBisim⟩ :=
    forward_single_step_nu_listener_derived
      (N := N) x P "n_init" "v_init" nuListenerBody
  obtain ⟨Tseed, hseedStep, hseedBisim⟩ :=
    forward_single_step_nameServer_listener_derived
      (N := N) "ns_x" "ns_z" "v_init" "ns_seed" seedListenerBody
  obtain ⟨Trep, hrepStep, hrepBisim⟩ :=
    forward_single_step_replicate_derived
      (N := N) "ns_x" "_drop" .nil "n_init" "v_init"
  let srcNu : Pattern :=
    rhoPar (encode (.nu x P) "n_init" "v_init")
      (.apply "PInput" [.fvar "v_init", .lambda none nuListenerBody])
  let srcSeed : Pattern :=
    rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
      (.apply "PInput" [.fvar "ns_z", .lambda none seedListenerBody])
  let srcRep : Pattern :=
    encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"
  let hnu : srcNu ⇝ᵈ* Tnu := Classical.choice hnuStep
  let hseed : srcSeed ⇝ᵈ* Tseed := Classical.choice hseedStep
  let hrep : srcRep ⇝ᵈ* Trep := Classical.choice hrepStep
  have hnuLift :
      (.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
      (.collection .hashBag [Tnu, srcSeed, srcRep] none) :=
    ReducesDerivedStar.par_any (before := ([] : List Pattern)) (after := [srcSeed, srcRep]) hnu
  have hseedLift :
      (.collection .hashBag [Tnu, srcSeed, srcRep] none) ⇝ᵈ*
      (.collection .hashBag [Tnu, Tseed, srcRep] none) :=
    ReducesDerivedStar.par_any (before := [Tnu]) (after := [srcRep]) hseed
  have hrepLift :
      (.collection .hashBag [Tnu, Tseed, srcRep] none) ⇝ᵈ*
      (.collection .hashBag [Tnu, Tseed, Trep] none) :=
    ReducesDerivedStar.par_any (before := [Tnu, Tseed]) (after := ([] : List Pattern)) hrep
  have htrace :
      (.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
      (.collection .hashBag [Tnu, Tseed, Trep] none) :=
    ReducesDerivedStar.trans hnuLift (ReducesDerivedStar.trans hseedLift hrepLift)
  have hswap :
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) := by
    exact (commute_nu_seed_admin_steps_under_bag_perm hnu hseed).2
  refine ⟨Tnu, Tseed, Trep, rfl, ?_, hswap, hnuBisim, hseedBisim, hrepBisim⟩
  simpa [srcNu, srcSeed, srcRep] using (show Nonempty
    ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
      (.collection .hashBag [Tnu, Tseed, Trep] none)) from ⟨htrace⟩)

/-- Full non-RF forward correspondence wrapper (derived layer):
combines generic replication-unfold and full-encode ν administrative closure. -/
theorem full_nonRF_forward_correspondence_derived {N : Finset String}
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
             (.apply "PInput" [.fvar "v_init", .lambda none nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda none seedListenerBody]),
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
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) := by
  refine ⟨?_, ?_⟩
  · simpa using
      (forward_single_step_replicate_derived
        (N := N) xr yr Pr n v)
  · simpa using
      (fullEncode_nu_admin_progress_combined_derived
        (N := N) x P nuListenerBody seedListenerBody)

/-- Freshness-threaded full non-RF forward correspondence wrapper. -/
theorem full_nonRF_forward_correspondence_derived_fresh {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String)
    (_hfresh : EncodingFresh P) :
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
             (.apply "PInput" [.fvar "v_init", .lambda none nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda none seedListenerBody]),
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
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) := by
  exact full_nonRF_forward_correspondence_derived
    (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v

/-- Concrete canary for packaged full-encode ν administrative progress. -/
theorem fullEncode_nu_admin_progress_derived_canary :
    fullEncode (.nu "x" .nil) =
      rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
    (∃ Tnu, Nonempty
      ((rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda none rhoNil])) ⇝ᵈ* Tnu) ∧
      Tnu ≈ᵈ{(∅ : Finset String)}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.fvar "n_init"),
           rhoInput (.fvar "n_init") "x" (encode .nil ("n_init" ++ "_" ++ "n_init") "v_init")] none)) ∧
    (∃ Tseed, Nonempty
      ((rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda none rhoNil])) ⇝ᵈ* Tseed) ∧
      Tseed ≈ᵈ{(∅ : Finset String)}
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none)) ∧
    (∃ Trep, Nonempty
      ((encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init") ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{(∅ : Finset String)}
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) := by
  simpa using
    (fullEncode_nu_admin_progress_derived
      (N := (∅ : Finset String)) "x" .nil rhoNil rhoNil)

/-- Concrete canary for the combined non-RF administrative closure theorem. -/
theorem fullEncode_nu_admin_progress_combined_derived_canary :
    ∃ Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda none rhoNil]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda none rhoNil]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.fvar "n_init"),
           rhoInput (.fvar "n_init") "x" (encode .nil ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Trep
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")) := by
  simpa using
    (fullEncode_nu_admin_progress_combined_derived
      (N := (∅ : Finset String)) "x" .nil rhoNil rhoNil)

/-- Nontrivial canary: combined closure with concrete non-`rhoNil` listener bodies. -/
theorem fullEncode_nu_admin_progress_combined_derived_canary_nontrivial :
    ∃ Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda none (.apply "PDrop" [.fvar "k"])]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda none (.apply "NQuote" [.fvar "m"])]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, Trep] none)) := by
  rcases
    (fullEncode_nu_admin_progress_combined_derived
      (N := (∅ : Finset String)) "x" .nil
      (.apply "PDrop" [.fvar "k"]) (.apply "NQuote" [.fvar "m"])) with
    ⟨Tnu, Tseed, Trep, hfull, htrace, _hswap, _hnu, _hseed, _hrep⟩
  exact ⟨Tnu, Tseed, Trep, hfull, htrace⟩

/-- Strong nontrivial canary:
combined closure with concrete non-`rhoNil` listener bodies, keeping swap and
all three endpoint bisim witnesses. -/
theorem fullEncode_nu_admin_progress_combined_derived_canary_nontrivial_full :
    ∃ Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda none (.apply "PDrop" [.fvar "k"])]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda none (.apply "NQuote" [.fvar "m"])]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
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
    (fullEncode_nu_admin_progress_combined_derived
      (N := (∅ : Finset String)) "x" .nil
      (.apply "PDrop" [.fvar "k"]) (.apply "NQuote" [.fvar "m"]))

/-- Regression endpoint: replicate-unfold specialized to `dropOperation "ns_x"`. -/
theorem forward_single_step_replicate_dropOperation_nsx_derived :
    ∃ T, Nonempty
      ((encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init") ⇝ᵈ* T) ∧
      T ≈ᵈ{(∅ : Finset String)}
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" rhoNil)
          (dropOperation "ns_x")) := by
  simpa [dropOperation, encode, rhoReplicate] using
    (forward_single_step_replicate_derived
      (N := (∅ : Finset String)) "ns_x" "_drop" .nil "n_init" "v_init")

/-! ## Forward Inventory (RF + Non-RF)

This module now exposes a no-gap forward result for the RF fragment via:
- `ForwardSimulation.forward_single_step_rf`
- `ForwardSimulation.forward_multi_step_rf`

Current non-RF derived endpoints:
- `forward_single_step_replicate_derived`
- `forward_single_step_nameServer_listener_derived`
- `forward_single_step_nu_listener_derived`
- `fullEncode_nu_admin_progress_derived`

Backward simulation and full non-RF π coverage still remain separate work.
-/

end Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
