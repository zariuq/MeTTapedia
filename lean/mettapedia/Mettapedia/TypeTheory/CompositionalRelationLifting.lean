import Mettapedia.GSLT.Core.RelationPresentation

/-! # Proof-relevant relation liftings preserving identity and composition -/
namespace Mettapedia.TypeTheory
universe u
/-- A proof-relevant data former may be used as a higher-order relational
lifting exactly when it preserves identity and relational composition
fibrewise.  These are equivalences of evidence types, not propositions about
Boolean support.

The structure deliberately does not claim strict equality: proof-relevant
composition is associative and unital through coherent equivalences. -/
structure CompositionalLifting (ObjectMap : Type u → Type u) where
  lift : {Source Target : Type u} →
    Mettapedia.GSLT.RelationPresentation.Rel Source Target → Mettapedia.GSLT.RelationPresentation.Rel (ObjectMap Source) (ObjectMap Target)
  identity : ∀ (Object : Type u) (source target : ObjectMap Object),
    (lift (Mettapedia.GSLT.RelationPresentation.Rel.graph id)).evidence source target ≃
      (Mettapedia.GSLT.RelationPresentation.Rel.graph id).evidence source target
  chain : ∀ {First Middle Last : Type u}
    (earlier : Mettapedia.GSLT.RelationPresentation.Rel First Middle)
    (later : Mettapedia.GSLT.RelationPresentation.Rel Middle Last)
    (source : ObjectMap First) (target : ObjectMap Last),
    (lift (Mettapedia.GSLT.RelationPresentation.Rel.Chain earlier later)).evidence source target ≃
      (Mettapedia.GSLT.RelationPresentation.Rel.Chain (lift earlier) (lift later)).evidence source target


end Mettapedia.TypeTheory
