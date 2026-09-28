import Mettapedia.Languages.Agda.SourceEvidence.ProofCode

/-! An executable decoder: malformed scope, indices, constructor parameters,
or ordered premise lists are rejected. Success contains actual source evidence. -/

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec
open Mettapedia.Languages.Agda.StaticSpecification

def decode : Code → Option Packed
  | .node 0 [] [] => do
      return ⟨.context .nil, FormCtx.nil ⟩
  | .node 1 [.atom n, cΓ, ca] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let h0 ← fit (.context Γ) (← decode p0)
      let h1 ← fit (.formation Γ a) (← decode p1)
      return ⟨.context (Γ.snoc a), FormCtx.snoc h0 h1⟩
  | .node 2 [.atom n, cΓ, .atom k, ct] [p0] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let h0 ← fit (.typing Γ t (Ty.universe k)) (← decode p0)
      return ⟨.formation Γ (.el k t), FormTy.ofTyping h0⟩
  | .node 3 [.atom n, cΓ, .atom k] [p0] => do
      let Γ ← decodeContext n cΓ
      let h0 ← fit (.context Γ) (← decode p0)
      return ⟨.typing Γ (.sort k) (Ty.universe (k + 1)), Typing.sort k h0⟩
  | .node 4 [.atom n, cΓ, .atom i] [p0] => do
      let Γ ← decodeContext n cΓ
      if bound : i < n then
        let i : Fin n := ⟨i, bound⟩
        let h0 ← fit (.context Γ) (← decode p0)
        return ⟨.typing Γ (.var i) (Γ.lookup i), Typing.var i h0⟩
      else none
  | .node 5 [.atom n, cΓ, ca, cb] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let b ← decodeTyAbs n cb
      let h0 ← fit (.formation Γ a) (← decode p0)
      let h1 ← fit (.formation (Γ.snoc a) b.open) (← decode p1)
      return ⟨.typing Γ (.pi a b) (Ty.universe (max a.level b.level)), Typing.pi h0 h1⟩
  | .node 6 [.atom n, cΓ, ca, cb, cbody] [p0, p1, p2] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let b ← decodeTyAbs n cb
      let body ← decodeAbs n cbody
      let h0 ← fit (.formation Γ a) (← decode p0)
      let h1 ← fit (.formation (Γ.snoc a) b.open) (← decode p1)
      let h2 ← fit (.typing (Γ.snoc a) body.open b.open) (← decode p2)
      return ⟨.typing Γ (.lam body) (Ty.pi a b), Typing.lam h0 h1 h2⟩
  | .node 7 [.atom n, cΓ, ca, cb, cf, cu] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let b ← decodeTyAbs n cb
      let f ← decodeTerm n cf
      let u ← decodeTerm n cu
      let h0 ← fit (.typing Γ f (Ty.pi a b)) (← decode p0)
      let h1 ← fit (.typing Γ u a) (← decode p1)
      return ⟨.typing Γ (f.app u) (b.instantiate u), Typing.app h0 h1⟩
  | .node 8 [.atom n, cΓ, ct, ca, cc] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let a ← decodeTy n ca
      let c ← decodeTy n cc
      let h0 ← fit (.typing Γ t a) (← decode p0)
      let h1 ← fit (.typeEquality Γ a c) (← decode p1)
      return ⟨.typing Γ t c, Typing.conv h0 h1⟩
  | .node 9 [.atom n, cΓ, .atom k, ct, cu] [p0] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let u ← decodeTerm n cu
      let h0 ← fit (.termEquality Γ t u (Ty.universe k)) (← decode p0)
      return ⟨.typeEquality Γ (.el k t) (.el k u), TypeEq.atSort h0⟩
  | .node 10 [.atom n, cΓ, ct, ca] [p0] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let a ← decodeTy n ca
      let h0 ← fit (.typing Γ t a) (← decode p0)
      return ⟨.termEquality Γ t t a, TermEq.refl h0⟩
  | .node 11 [.atom n, cΓ, ct, cu, ca] [p0] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let u ← decodeTerm n cu
      let a ← decodeTy n ca
      let h0 ← fit (.termEquality Γ t u a) (← decode p0)
      return ⟨.termEquality Γ u t a, TermEq.symm h0⟩
  | .node 12 [.atom n, cΓ, ct, cu, cv, ca] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let u ← decodeTerm n cu
      let v ← decodeTerm n cv
      let a ← decodeTy n ca
      let h0 ← fit (.termEquality Γ t u a) (← decode p0)
      let h1 ← fit (.termEquality Γ u v a) (← decode p1)
      return ⟨.termEquality Γ t v a, TermEq.trans h0 h1⟩
  | .node 13 [.atom n, cΓ, ct, cu, ca, cc] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let t ← decodeTerm n ct
      let u ← decodeTerm n cu
      let a ← decodeTy n ca
      let c ← decodeTy n cc
      let h0 ← fit (.termEquality Γ t u a) (← decode p0)
      let h1 ← fit (.typeEquality Γ a c) (← decode p1)
      return ⟨.termEquality Γ t u c, TermEq.conv h0 h1⟩
  | .node 14 [.atom n, cΓ, ca, ca2, cb, cb2] [p0, p1, p2] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let a2 ← decodeTy n ca2
      let b ← decodeTyAbs n cb
      let b2 ← decodeTyAbs n cb2
      let h0 ← fit (.formation Γ a) (← decode p0)
      let h1 ← fit (.typeEquality Γ a a2) (← decode p1)
      let h2 ← fit (.typeEquality (Γ.snoc a) b.open b2.open) (← decode p2)
      return ⟨.termEquality Γ (.pi a b) (.pi a2 b2) (Ty.universe (max a.level b.level)), TermEq.piCong h0 h1 h2⟩
  | .node 15 [.atom n, cΓ, ca, cb, cf, cg, cu, cv] [p0, p1] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let b ← decodeTyAbs n cb
      let f ← decodeTerm n cf
      let g ← decodeTerm n cg
      let u ← decodeTerm n cu
      let v ← decodeTerm n cv
      let h0 ← fit (.termEquality Γ f g (Ty.pi a b)) (← decode p0)
      let h1 ← fit (.termEquality Γ u v a) (← decode p1)
      return ⟨.termEquality Γ (f.app u) (g.app v) (b.instantiate u), TermEq.appCong h0 h1⟩
  | .node 16 [.atom n, cΓ, ca, cb, cbody, cu] [p0, p1, p2, p3] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let b ← decodeTyAbs n cb
      let body ← decodeAbs n cbody
      let u ← decodeTerm n cu
      let h0 ← fit (.formation Γ a) (← decode p0)
      let h1 ← fit (.formation (Γ.snoc a) b.open) (← decode p1)
      let h2 ← fit (.typing (Γ.snoc a) body.open b.open) (← decode p2)
      let h3 ← fit (.typing Γ u a) (← decode p3)
      return ⟨.termEquality Γ ((Term.lam body).app u) (body.instantiate u) (b.instantiate u), TermEq.beta h0 h1 h2 h3⟩
  | .node 17 [.atom n, cΓ, ca, cb, cf, cg] [p0, p1, p2, p3, p4] => do
      let Γ ← decodeContext n cΓ
      let a ← decodeTy n ca
      let b ← decodeTyAbs n cb
      let f ← decodeTerm n cf
      let g ← decodeTerm n cg
      let h0 ← fit (.formation Γ a) (← decode p0)
      let h1 ← fit (.formation (Γ.snoc a) b.open) (← decode p1)
      let h2 ← fit (.typing Γ f (Ty.pi a b)) (← decode p2)
      let h3 ← fit (.typing Γ g (Ty.pi a b)) (← decode p3)
      let h4 ← fit (.termEquality (Γ.snoc a) (f.weaken.app (.var 0)) (g.weaken.app (.var 0)) b.open) (← decode p4)
      return ⟨.termEquality Γ f g (Ty.pi a b), TermEq.eta h0 h1 h2 h3 h4⟩
  | _ => none

/-- Check a code against a requested complete source index. -/
def decodeAt (expected : Judgment) (code : Code) : Option (Evidence expected) := do
  fit expected (← decode code)

end Mettapedia.Languages.Agda.SourceEvidence.Codec
