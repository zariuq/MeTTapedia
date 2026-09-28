import Mettapedia.Languages.Agda.SourceEvidence.JudgmentCode

/-! Serialization of the eighteen constructors in the frozen source Judgments module.
Every constructor parameter and every ordered premise is retained. -/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec
open Mettapedia.Languages.Agda.StaticSpecification

mutual
  def encodeFormCtx {Γ : RawContext n} (d : FormCtx Γ) : Code :=
    match d with
    | @FormCtx.nil  =>
        .node 0 []
          []
    | @FormCtx.snoc n Γ a h0 h1 =>
        .node 1 [.atom n, encodeContext Γ, encodeTy a]
          [encodeFormCtx h0, encodeFormTy h1]
  def encodeFormTy {Γ : RawContext n} {a : Ty n} (d : FormTy Γ a) : Code :=
    match d with
    | @FormTy.ofTyping n Γ k t h0 =>
        .node 2 [.atom n, encodeContext Γ, .atom k, encodeTerm t]
          [encodeTyping h0]
  def encodeTyping {Γ : RawContext n} {t : Term n} {a : Ty n} (d : Typing Γ t a) : Code :=
    match d with
    | @Typing.sort n Γ k h0 =>
        .node 3 [.atom n, encodeContext Γ, .atom k]
          [encodeFormCtx h0]
    | @Typing.var n Γ i h0 =>
        .node 4 [.atom n, encodeContext Γ, .atom i.val]
          [encodeFormCtx h0]
    | @Typing.pi n Γ a b h0 h1 =>
        .node 5 [.atom n, encodeContext Γ, encodeTy a, encodeTyAbs b]
          [encodeFormTy h0, encodeFormTy h1]
    | @Typing.lam n Γ a b body h0 h1 h2 =>
        .node 6 [.atom n, encodeContext Γ, encodeTy a, encodeTyAbs b, encodeAbs body]
          [encodeFormTy h0, encodeFormTy h1, encodeTyping h2]
    | @Typing.app n Γ a b f u h0 h1 =>
        .node 7 [.atom n, encodeContext Γ, encodeTy a, encodeTyAbs b, encodeTerm f, encodeTerm u]
          [encodeTyping h0, encodeTyping h1]
    | @Typing.conv n Γ t a c h0 h1 =>
        .node 8 [.atom n, encodeContext Γ, encodeTerm t, encodeTy a, encodeTy c]
          [encodeTyping h0, encodeTypeEq h1]
  def encodeTypeEq {Γ : RawContext n} {a c : Ty n} (d : TypeEq Γ a c) : Code :=
    match d with
    | @TypeEq.atSort n Γ k t u h0 =>
        .node 9 [.atom n, encodeContext Γ, .atom k, encodeTerm t, encodeTerm u]
          [encodeTermEq h0]
  def encodeTermEq {Γ : RawContext n} {t u : Term n} {a : Ty n} (d : TermEq Γ t u a) : Code :=
    match d with
    | @TermEq.refl n Γ t a h0 =>
        .node 10 [.atom n, encodeContext Γ, encodeTerm t, encodeTy a]
          [encodeTyping h0]
    | @TermEq.symm n Γ t u a h0 =>
        .node 11 [.atom n, encodeContext Γ, encodeTerm t, encodeTerm u, encodeTy a]
          [encodeTermEq h0]
    | @TermEq.trans n Γ t u v a h0 h1 =>
        .node 12 [.atom n, encodeContext Γ, encodeTerm t, encodeTerm u, encodeTerm v, encodeTy a]
          [encodeTermEq h0, encodeTermEq h1]
    | @TermEq.conv n Γ t u a c h0 h1 =>
        .node 13 [.atom n, encodeContext Γ, encodeTerm t, encodeTerm u, encodeTy a, encodeTy c]
          [encodeTermEq h0, encodeTypeEq h1]
    | @TermEq.piCong n Γ a a2 b b2 h0 h1 h2 =>
        .node 14 [.atom n, encodeContext Γ, encodeTy a, encodeTy a2, encodeTyAbs b, encodeTyAbs b2]
          [encodeFormTy h0, encodeTypeEq h1, encodeTypeEq h2]
    | @TermEq.appCong n Γ a b f g u v h0 h1 =>
        .node 15 [.atom n, encodeContext Γ, encodeTy a, encodeTyAbs b, encodeTerm f, encodeTerm g, encodeTerm u, encodeTerm v]
          [encodeTermEq h0, encodeTermEq h1]
    | @TermEq.beta n Γ a b body u h0 h1 h2 h3 =>
        .node 16 [.atom n, encodeContext Γ, encodeTy a, encodeTyAbs b, encodeAbs body, encodeTerm u]
          [encodeFormTy h0, encodeFormTy h1, encodeTyping h2, encodeTyping h3]
    | @TermEq.eta n Γ a b f g h0 h1 h2 h3 h4 =>
        .node 17 [.atom n, encodeContext Γ, encodeTy a, encodeTyAbs b, encodeTerm f, encodeTerm g]
          [encodeFormTy h0, encodeFormTy h1, encodeTyping h2, encodeTyping h3, encodeTermEq h4]
end

def encodePacked (packet : Packed) : Code :=
  match packet with
  | ⟨.context _, d⟩ => encodeFormCtx d
  | ⟨.formation _ _, d⟩ => encodeFormTy d
  | ⟨.typing _ _ _, d⟩ => encodeTyping d
  | ⟨.typeEquality _ _ _, d⟩ => encodeTypeEq d
  | ⟨.termEquality _ _ _ _, d⟩ => encodeTermEq d

end Mettapedia.Languages.Agda.SourceEvidence.Codec
