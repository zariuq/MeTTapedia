import Mettapedia.Languages.Agda.SourceEvidence.DecodeProof

/-! Exact source-proof reconstruction, including all ordered derivation histories. -/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec
open Mettapedia.Languages.Agda.StaticSpecification

mutual
  @[simp] theorem decode_encodeFormCtx {Γ : RawContext n} (d : FormCtx Γ) :
      decode (encodeFormCtx d) = some ⟨.context Γ, d⟩ := by
    match d with
    | @FormCtx.nil  =>
        rfl
    | @FormCtx.snoc n Γ a h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let d0 ← fit (.context Γ) (← decode (encodeFormCtx h0))
          let d1 ← fit (.formation Γ a) (← decode (encodeFormTy h1))
          return ⟨.context (Γ.snoc a), FormCtx.snoc d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeFormCtx h0, decode_encodeFormTy h1]
  @[simp] theorem decode_encodeFormTy {Γ : RawContext n} {a : Ty n} (d : FormTy Γ a) :
      decode (encodeFormTy d) = some ⟨.formation Γ a, d⟩ := by
    match d with
    | @FormTy.ofTyping n Γ k t h0 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let d0 ← fit (.typing Γ t (Ty.universe k)) (← decode (encodeTyping h0))
          return ⟨.formation Γ (.el k t), FormTy.ofTyping d0⟩) = _
        simp [fit, Option.bind, decode_encodeTyping h0]
  @[simp] theorem decode_encodeTyping {Γ : RawContext n} {t : Term n} {a : Ty n} (d : Typing Γ t a) :
      decode (encodeTyping d) = some ⟨.typing Γ t a, d⟩ := by
    match d with
    | @Typing.sort n Γ k h0 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let d0 ← fit (.context Γ) (← decode (encodeFormCtx h0))
          return ⟨.typing Γ (.sort k) (Ty.universe (k + 1)), Typing.sort k d0⟩) = _
        simp [fit, Option.bind, decode_encodeFormCtx h0]
    | @Typing.var n Γ i h0 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          if bound : i.val < n then
            let i : Fin n := ⟨i.val, bound⟩
            let d0 ← fit (.context Γ) (← decode (encodeFormCtx h0))
            return ⟨.typing Γ (.var i) (Γ.lookup i), Typing.var i d0⟩
          else none) = _
        simp [fit, Option.bind, decode_encodeFormCtx h0]
    | @Typing.pi n Γ a b h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let d0 ← fit (.formation Γ a) (← decode (encodeFormTy h0))
          let d1 ← fit (.formation (Γ.snoc a) b.open) (← decode (encodeFormTy h1))
          return ⟨.typing Γ (.pi a b) (Ty.universe (max a.level b.level)), Typing.pi d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeFormTy h0, decode_encodeFormTy h1]
    | @Typing.lam n Γ a b body h0 h1 h2 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let body ← decodeAbs n (encodeAbs body)
          let d0 ← fit (.formation Γ a) (← decode (encodeFormTy h0))
          let d1 ← fit (.formation (Γ.snoc a) b.open) (← decode (encodeFormTy h1))
          let d2 ← fit (.typing (Γ.snoc a) body.open b.open) (← decode (encodeTyping h2))
          return ⟨.typing Γ (.lam body) (Ty.pi a b), Typing.lam d0 d1 d2⟩) = _
        simp [fit, Option.bind, decode_encodeFormTy h0, decode_encodeFormTy h1, decode_encodeTyping h2]
    | @Typing.app n Γ a b f u h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let f ← decodeTerm n (encodeTerm f)
          let u ← decodeTerm n (encodeTerm u)
          let d0 ← fit (.typing Γ f (Ty.pi a b)) (← decode (encodeTyping h0))
          let d1 ← fit (.typing Γ u a) (← decode (encodeTyping h1))
          return ⟨.typing Γ (f.app u) (b.instantiate u), Typing.app d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeTyping h0, decode_encodeTyping h1]
    | @Typing.conv n Γ t a c h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let a ← decodeTy n (encodeTy a)
          let c ← decodeTy n (encodeTy c)
          let d0 ← fit (.typing Γ t a) (← decode (encodeTyping h0))
          let d1 ← fit (.typeEquality Γ a c) (← decode (encodeTypeEq h1))
          return ⟨.typing Γ t c, Typing.conv d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeTyping h0, decode_encodeTypeEq h1]
  @[simp] theorem decode_encodeTypeEq {Γ : RawContext n} {a c : Ty n} (d : TypeEq Γ a c) :
      decode (encodeTypeEq d) = some ⟨.typeEquality Γ a c, d⟩ := by
    match d with
    | @TypeEq.atSort n Γ k t u h0 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let u ← decodeTerm n (encodeTerm u)
          let d0 ← fit (.termEquality Γ t u (Ty.universe k)) (← decode (encodeTermEq h0))
          return ⟨.typeEquality Γ (.el k t) (.el k u), TypeEq.atSort d0⟩) = _
        simp [fit, Option.bind, decode_encodeTermEq h0]
  @[simp] theorem decode_encodeTermEq {Γ : RawContext n} {t u : Term n} {a : Ty n} (d : TermEq Γ t u a) :
      decode (encodeTermEq d) = some ⟨.termEquality Γ t u a, d⟩ := by
    match d with
    | @TermEq.refl n Γ t a h0 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let a ← decodeTy n (encodeTy a)
          let d0 ← fit (.typing Γ t a) (← decode (encodeTyping h0))
          return ⟨.termEquality Γ t t a, TermEq.refl d0⟩) = _
        simp [fit, Option.bind, decode_encodeTyping h0]
    | @TermEq.symm n Γ t u a h0 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let u ← decodeTerm n (encodeTerm u)
          let a ← decodeTy n (encodeTy a)
          let d0 ← fit (.termEquality Γ t u a) (← decode (encodeTermEq h0))
          return ⟨.termEquality Γ u t a, TermEq.symm d0⟩) = _
        simp [fit, Option.bind, decode_encodeTermEq h0]
    | @TermEq.trans n Γ t u v a h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let u ← decodeTerm n (encodeTerm u)
          let v ← decodeTerm n (encodeTerm v)
          let a ← decodeTy n (encodeTy a)
          let d0 ← fit (.termEquality Γ t u a) (← decode (encodeTermEq h0))
          let d1 ← fit (.termEquality Γ u v a) (← decode (encodeTermEq h1))
          return ⟨.termEquality Γ t v a, TermEq.trans d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeTermEq h0, decode_encodeTermEq h1]
    | @TermEq.conv n Γ t u a c h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let t ← decodeTerm n (encodeTerm t)
          let u ← decodeTerm n (encodeTerm u)
          let a ← decodeTy n (encodeTy a)
          let c ← decodeTy n (encodeTy c)
          let d0 ← fit (.termEquality Γ t u a) (← decode (encodeTermEq h0))
          let d1 ← fit (.typeEquality Γ a c) (← decode (encodeTypeEq h1))
          return ⟨.termEquality Γ t u c, TermEq.conv d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeTermEq h0, decode_encodeTypeEq h1]
    | @TermEq.piCong n Γ a a2 b b2 h0 h1 h2 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let a2 ← decodeTy n (encodeTy a2)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let b2 ← decodeTyAbs n (encodeTyAbs b2)
          let d0 ← fit (.formation Γ a) (← decode (encodeFormTy h0))
          let d1 ← fit (.typeEquality Γ a a2) (← decode (encodeTypeEq h1))
          let d2 ← fit (.typeEquality (Γ.snoc a) b.open b2.open) (← decode (encodeTypeEq h2))
          return ⟨.termEquality Γ (.pi a b) (.pi a2 b2) (Ty.universe (max a.level b.level)), TermEq.piCong d0 d1 d2⟩) = _
        simp [fit, Option.bind, decode_encodeFormTy h0, decode_encodeTypeEq h1, decode_encodeTypeEq h2]
    | @TermEq.appCong n Γ a b f g u v h0 h1 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let f ← decodeTerm n (encodeTerm f)
          let g ← decodeTerm n (encodeTerm g)
          let u ← decodeTerm n (encodeTerm u)
          let v ← decodeTerm n (encodeTerm v)
          let d0 ← fit (.termEquality Γ f g (Ty.pi a b)) (← decode (encodeTermEq h0))
          let d1 ← fit (.termEquality Γ u v a) (← decode (encodeTermEq h1))
          return ⟨.termEquality Γ (f.app u) (g.app v) (b.instantiate u), TermEq.appCong d0 d1⟩) = _
        simp [fit, Option.bind, decode_encodeTermEq h0, decode_encodeTermEq h1]
    | @TermEq.beta n Γ a b body u h0 h1 h2 h3 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let body ← decodeAbs n (encodeAbs body)
          let u ← decodeTerm n (encodeTerm u)
          let d0 ← fit (.formation Γ a) (← decode (encodeFormTy h0))
          let d1 ← fit (.formation (Γ.snoc a) b.open) (← decode (encodeFormTy h1))
          let d2 ← fit (.typing (Γ.snoc a) body.open b.open) (← decode (encodeTyping h2))
          let d3 ← fit (.typing Γ u a) (← decode (encodeTyping h3))
          return ⟨.termEquality Γ ((Term.lam body).app u) (body.instantiate u) (b.instantiate u), TermEq.beta d0 d1 d2 d3⟩) = _
        simp [fit, Option.bind, decode_encodeFormTy h0, decode_encodeFormTy h1, decode_encodeTyping h2, decode_encodeTyping h3]
    | @TermEq.eta n Γ a b f g h0 h1 h2 h3 h4 =>
        change (show Option Packed from do
          let Γ ← decodeContext n (encodeContext Γ)
          let a ← decodeTy n (encodeTy a)
          let b ← decodeTyAbs n (encodeTyAbs b)
          let f ← decodeTerm n (encodeTerm f)
          let g ← decodeTerm n (encodeTerm g)
          let d0 ← fit (.formation Γ a) (← decode (encodeFormTy h0))
          let d1 ← fit (.formation (Γ.snoc a) b.open) (← decode (encodeFormTy h1))
          let d2 ← fit (.typing Γ f (Ty.pi a b)) (← decode (encodeTyping h2))
          let d3 ← fit (.typing Γ g (Ty.pi a b)) (← decode (encodeTyping h3))
          let d4 ← fit (.termEquality (Γ.snoc a) (f.weaken.app (.var 0)) (g.weaken.app (.var 0)) b.open) (← decode (encodeTermEq h4))
          return ⟨.termEquality Γ f g (Ty.pi a b), TermEq.eta d0 d1 d2 d3 d4⟩) = _
        simp [fit, Option.bind, decode_encodeFormTy h0, decode_encodeFormTy h1, decode_encodeTyping h2, decode_encodeTyping h3, decode_encodeTermEq h4]
end

@[simp] theorem decode_encodePacked (packet : Packed) :
    decode (encodePacked packet) = some packet := by
  obtain ⟨j, d⟩ := packet
  cases j with
  | context => exact decode_encodeFormCtx d
  | formation => exact decode_encodeFormTy d
  | typing => exact decode_encodeTyping d
  | typeEquality => exact decode_encodeTypeEq d
  | termEquality => exact decode_encodeTermEq d

@[simp] theorem decodeAt_encodePacked (j : Judgment) (d : Evidence j) :
    decodeAt j (encodePacked ⟨j, d⟩) = some d := by
  simp [decodeAt, fit, Option.bind]

theorem encodePacked_injective : Function.Injective encodePacked := by
  intro left right equal
  have := congrArg decode equal
  simpa using this

theorem encodeEvidence_injective (j : Judgment) :
    Function.Injective (fun d : Evidence j => encodePacked ⟨j, d⟩) := by
  intro left right equal
  have := encodePacked_injective equal
  cases this
  rfl

end Mettapedia.Languages.Agda.SourceEvidence.Codec
