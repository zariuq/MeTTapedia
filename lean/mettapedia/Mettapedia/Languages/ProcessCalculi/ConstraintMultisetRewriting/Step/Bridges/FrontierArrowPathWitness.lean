import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowRuns
import Mettapedia.GSLT.Core.CorrespondencePathWitness

/-!
# Path bisimulation of the actual source and whole-frontier controller

The observation is the complete bag of closed-reading sets, rather than a
constant predicate or only its support. The existing correspondence supplies
the actual representation and step laws. Positive execution and termination
transport remain the separate certificates in `FrontierArrowRuns`.

This is an instance of the existing path-bisimulation interface on the sum
of the two state carriers. It constructs no category of models and asserts
no bijection between controller steps and individual native firings.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.CategoryTheory.GeneralizedOpenMaps
open SourceLanguage Hosting

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  (supply : Nat → Term S Γ star) (spaces : Term S Γ star → Multiset (Row κ Γ star))
  (q : Comp κ Γ star D.Ty)
  (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
  {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
  (arrowQ : ArrowComp q)

def bagPathWitness :
    PathWitness (CorrespondencePathWitness.sumKit (source P supply) (target N P)
      (Multiset (Set (Term S Γ star)))
      (fun configuration bag => configuration.answers (D := D) = bag)
      (fun frontier bag => answers N frontier = bag)) :=
  CorrespondencePathWitness.pathWitness
    (correspondence N P supply spaces q equations qScoped qDistinct arrowQ) _ _ _
    (fun represented _ => by rw [answers_eq N P supply spaces q represented])

include equations qScoped qDistinct arrowQ

theorem initial_bag_path_bisim :
    PathBisim (CorrespondencePathWitness.sumKit (source P supply) (target N P)
      (Multiset (Set (Term S Γ star)))
      (fun configuration bag => configuration.answers (D := D) = bag)
      (fun frontier bag => answers N frontier = bag))
      (.inl (Config.initial spaces q)) (.inr (initialState N P q)) := by
  refine ⟨bagPathWitness N P supply spaces q equations qScoped qDistinct arrowQ, ?_⟩
  exact initial_related N P supply spaces q arrowQ (query_unopened qScoped qDistinct arrowQ)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow.initial_bag_path_bisim
