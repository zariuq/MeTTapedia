import Mettapedia.Languages.Agda.StaticSpecification.Judgments

/-! Context formation is recovered from the actual static derivation trees. -/

namespace Mettapedia.Languages.Agda.StaticSpecification

mutual
  def FormTy.context {Γ : RawContext n} {a : Ty n} (d : FormTy Γ a) : FormCtx Γ :=
    match d with | .ofTyping h => h.context

  def Typing.context {Γ : RawContext n} {t : Term n} {a : Ty n}
      (d : Typing Γ t a) : FormCtx Γ :=
    match d with
    | .sort _ h => h
    | .var _ h => h
    | .pi h _ => h.context
    | .lam h _ _ => h.context
    | .app h _ => h.context
    | .conv h _ => h.context
end

mutual
  def TypeEq.context {Γ : RawContext n} {a b : Ty n} (d : TypeEq Γ a b) : FormCtx Γ :=
    match d with | .atSort h => h.context

  def TermEq.context {Γ : RawContext n} {t u : Term n} {a : Ty n}
      (d : TermEq Γ t u a) : FormCtx Γ :=
    match d with
    | .refl h => h.context
    | .symm h => h.context
    | .trans h _ => h.context
    | .conv h _ => h.context
    | .piCong h _ _ => h.context
    | .appCong h _ => h.context
    | .beta h _ _ _ => h.context
    | .eta h _ _ _ _ => h.context
end

/-- Noncumulative conversion preserves the complete finite sort annotation. -/
theorem TypeEq.level_eq {Γ : RawContext n} {a b : Ty n} (d : TypeEq Γ a b) :
    a.level = b.level := by cases d; rfl

/-- Even through arbitrarily many conversion rules, a universe keeps its sort. -/
theorem Typing.sort_level {Γ : RawContext n} {k : Nat} {a : Ty n}
    (d : Typing Γ (.sort k) a) : a.level = k + 2 := by
  cases d with
  | sort => rfl
  | conv h e => exact e.level_eq ▸ h.sort_level
termination_by sizeOf d

/-- A sort term is formed only with its successor annotation. -/
theorem FormTy.sort_annotation {Γ : RawContext n} {j k : Nat}
    (d : FormTy Γ (.el k (.sort j))) : k = j + 1 := by
  cases d with
  | ofTyping h => exact Nat.succ.inj h.sort_level

end Mettapedia.Languages.Agda.StaticSpecification
