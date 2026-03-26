import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Name Server Progress Lemmas

Operational lemmas for the Lybech-style name server used by the π→ρ encoding.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-- Request/response progress against the initial seed:
    a listener on `z` can consume the seed output from `nameServer` in one
    derived step (via core COMM wrapped by structural congruence). -/
theorem nameServer_request_response_progress_general
    (x z v s : String) (body : Pattern) :
    Nonempty
      ((rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda none body])) ⇝ᵈ*
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst body (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none)) := by
  let listener : Pattern := .apply "PInput" [.fvar z, .lambda none body]
  let rep : Pattern := rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v)
  let dropX : Pattern := dropOperation x
  let out : Pattern := rhoOutput (.fvar z) (.apply "PDrop" [.fvar s])
  let src : Pattern := rhoPar (nameServer x z v s) listener
  let preComm : Pattern := .collection .hashBag [out, listener, rep, dropX] none
  let tgt : Pattern := .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst body (.apply "PDrop" [.fvar s]), rep, dropX] none
  have hdecomp :=
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nameServer_listener_comm_decompose
      x z v s body
  have hpre : src ≡ preComm := by
    exact (by simpa
      [src, preComm, listener, rep, dropX, out,
       Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nameServerListenerSource,
       Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nameServerListenerPreComm]
      using hdecomp.1)
  have hcomm : preComm ⇝ tgt := by
    exact (by simpa
      [tgt, rep, dropX,
       Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nameServerListenerTarget]
      using (Classical.choice hdecomp.2))
  have hcore : src ⇝ tgt := by
    exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
      hpre hcomm (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
  exact ⟨ReducesDerivedStar.single (.core hcore)⟩

/-- Specialized request/response progress used by regression tests. -/
theorem nameServer_request_response_progress (x z v s : String) :
    Nonempty
      ((rhoPar (nameServer x z v s) (rhoInput (.fvar z) "u" rhoNil)) ⇝ᵈ*
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none)) := by
  simpa [rhoInput, rhoNil, Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar] using
    nameServer_request_response_progress_general x z v s rhoNil

/-- Concrete canary instance for CI/regression checks on name-server seed COMM. -/
theorem nameServer_request_response_progress_canary :
    Nonempty
      ((rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
         (rhoInput (.fvar "ns_z") "u" rhoNil)) ⇝ᵈ*
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst rhoNil (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none)) := by
  simpa using
    nameServer_request_response_progress "ns_x" "ns_z" "v_init" "ns_seed"

end Mettapedia.Languages.ProcessCalculi.PiCalculus
