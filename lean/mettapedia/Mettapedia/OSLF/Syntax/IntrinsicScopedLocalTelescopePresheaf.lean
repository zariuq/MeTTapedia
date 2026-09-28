import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution
import Mettapedia.OSLF.Syntax.BindingTelescopeCwf
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory
import Mettapedia.GSLT.Topos.ConstructivePresheafOperations

/-!
# Local computation histories over raw telescopes

The actual rule-local firing trees form an event presheaf over the raw
telescope category. Its action is the proved binder-aware substitution on
trees. Both endpoints are natural transformations. No typing evidence is
selected or erased to define this action; admission can restrict the base
later by ordinary precomposition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalTelescopePresheaf

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open IntrinsicScopedLocalPolynomial
open IntrinsicScopedConditionalSubstitution (substJudgment substJudgment_identity substJudgment_comp)
open Mettapedia.GSLT.Topos.ConstructivePresheaf (EventGraph)

variable {S : Signature} (R : List (LocalRule S))

/-- Endpoints and the entire ordered firing history, at one ordinary scope. -/
structure Event (Γ : Ctx S) (s : S.Srt) where
  source : Term S Γ s
  target : Term S Γ s
  history : Tree R (BindingCloneAlgebra.terms S) ⟨Γ, s, source, target⟩

namespace Event

@[ext] theorem ext {Γ : Ctx S} {s : S.Srt} {first second : Event R Γ s}
    (source : first.source = second.source) (target : first.target = second.target)
    (history : HEq first.history second.history) : first = second := by
  cases first
  cases second
  cases source
  cases target
  cases history
  rfl

noncomputable def substitute {Γ Δ : Ctx S} {s : S.Srt}
    (σ : Sub S Γ Δ) (event : Event R Γ s) : Event R Δ s where
  source := bind σ event.source
  target := bind σ event.target
  history := substTree R (BindingCloneAlgebra.terms S) _ event.history σ _ rfl

theorem substitute_identity {Γ : Ctx S} {s : S.Srt} (event : Event R Γ s) :
    substitute R (fun _ v => .var v) event = event := by
  refine ext R (bind_id event.source) (bind_id event.target) ?_
  let j : AuthoredPositionedRulePolynomial.Judgment (BindingCloneAlgebra.terms S) :=
    ⟨Γ, s, event.source, event.target⟩
  have hj := substJudgment_identity j
  exact (substTree_congr R (BindingCloneAlgebra.terms S) event.history rfl hj rfl hj).trans
    (heq_of_eq (substTree_identity R (BindingCloneAlgebra.terms S) j event.history hj))

theorem substitute_comp {Γ Δ Θ : Ctx S} {s : S.Srt}
    (σ : Sub S Γ Δ) (τ : Sub S Δ Θ) (event : Event R Γ s) :
    substitute R τ (substitute R σ event) =
      substitute R (fun sort v => bind τ (σ sort v)) event := by
  refine ext R (bind_comp σ τ event.source) (bind_comp σ τ event.target) ?_
  let A := BindingCloneAlgebra.terms S
  let j : AuthoredPositionedRulePolynomial.Judgment A :=
    ⟨Γ, s, event.source, event.target⟩
  have hj := substJudgment_comp j σ τ
  exact (substTree_congr R A
      (substTree R A j event.history σ (substJudgment j σ) rfl)
      rfl hj rfl hj).trans
    (heq_of_eq (substTree_comp R A j event.history σ τ _ hj rfl))

end Event

variable (b k : S.Srt)

abbrev Base (S : Signature) (b k : S.Srt) :=
  (Telescope.rawTelescopeCwf S b k).base.Contextᵒᵖ

/-- Terms of any signature sort over the actual raw telescope base. -/
def terms (S : Signature) (b k s : S.Srt) : Base S b k ⥤ Type where
  obj X := Term S (Telescope.scope b X.unop.val.1) s
  map f := TypeCat.ofHom (bind f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro term
    exact bind_id term
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro term
    exact (bind_comp f.unop g.unop term).symm

/-- Substitution retains the whole computation tree and its rule identities. -/
noncomputable def events (s : S.Srt) : Base S b k ⥤ Type where
  obj X := Event R (Telescope.scope b X.unop.val.1) s
  map f := TypeCat.ofHom (Event.substitute R f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact Event.substitute_identity R event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact (Event.substitute_comp R f.unop g.unop event).symm

noncomputable def source (s : S.Srt) : NatTrans (events R b k s) (terms S b k s) where
  app _ := TypeCat.ofHom Event.source
  naturality _ _ _ := rfl

noncomputable def target (s : S.Srt) : NatTrans (events R b k s) (terms S b k s) where
  app _ := TypeCat.ofHom Event.target
  naturality _ _ _ := rfl

/-- The internal graph uses the given rule table, without a new evaluator. -/
noncomputable def graph (s : S.Srt) : EventGraph (Base S b k) where
  vertex := terms S b k s
  edge := events R b k s
  source := source R b k s
  target := target R b k s

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalTelescopePresheaf
