import Mettapedia.OSLF.Syntax.SignatureMorphism
import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Strict signature maps on equational theories

Generator checks cover contextual metavariable bodies together with their
ambient and ordinary environments. The derived transport theorem handles
arbitrary context maps, equivalence closure, and congruence under binders.
The sort map need not be injective: translated substitutions are indexed by
variable positions, rather than by an inverse on sorts.

The generator obligation does not yet construct translated equation schemas
over a mapped metavariable signature. That separate construction can discharge
the obligation here; arbitrary closure preservation is not assumed.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S T : Signature}

/-- Translate a substitution into an arbitrary target context. -/
def SigMor.mapSub (F : SigMor S T) {Γ' : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ' Δ) : {Γ : Ctx S} → Sub S Γ Γ' →
      Sub T (Γ.map F.sortMap) Δ
  | [], _, _, x => nomatch x
  | _ :: _, σ, _, .zero => mapTerm F ν (σ _ .zero)
  | _ :: _, σ, _, .succ x => F.mapSub ν (fun s y => σ s (.succ y)) _ x

theorem SigMor.mapSub_mapVar (F : SigMor S T) {Γ' : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ' Δ) :
    ∀ {Γ : Ctx S} (σ : Sub S Γ Γ') (s : S.Srt) (x : Var Γ s),
      F.mapSub ν σ (F.sortMap s) (mapVar F.sortMap s x) = mapTerm F ν (σ s x)
  | _ :: _, _, _, .zero => rfl
  | _ :: _, σ, _, .succ x => F.mapSub_mapVar ν (fun s y => σ s (.succ y)) _ x

/-- Substitution compatibility, with the target substitution constructed. -/
theorem SigMor.map_bind (F : SigMor S T) {Γ Γ' : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ' Δ) (σ : Sub S Γ Γ') {s : S.Srt}
    (t : Term S Γ s) :
    mapTerm F ν (bind σ t) = bind (F.mapSub ν σ) (F.onTerm t) :=
  mapTerm_bind F (mapVar F.sortMap) ν σ (F.mapSub ν σ)
    (F.mapSub_mapVar ν σ) t

/-- Every contextual generator, including independent ambient and ordinary
environments, must be justified in its mapped result context. -/
def SigMor.RespectsEquations (F : SigMor S T)
    {M : List (MetaArity S)} {N : List (MetaArity T)}
    (E : List (EqAxiom S M)) (D : List (EqAxiom T N)) : Prop :=
  ∀ (i : Fin E.length) {Θ Γ : Ctx S}
    (body : ContextualAssignment S M Θ) (ambient : Sub S Θ Γ)
    (ordinary : Sub S (E.get i).ctx Γ),
    EqClosure D (F.onTerm (ContextualAssignment.instantiate body ambient ordinary (E.get i).lhs))
      (F.onTerm (ContextualAssignment.instantiate body ambient ordinary (E.get i).rhs))

theorem eqArgs_castArity {N : List (MetaArity T)} {D : List (EqAxiom T N)}
    {as bs : List (List T.Srt × T.Srt)} {Γ : Ctx T} (h : as = bs)
    {a b : Args T as Γ} (hab : EqArgs D a b) :
    EqArgs D (castArgsArity h a) (castArgsArity h b) := by
  subst h
  exact hab

mutual
/-- Transport the whole equational theory from its generator obligations. -/
theorem SigMor.eqClosure_map (F : SigMor S T)
    {M : List (MetaArity S)} {N : List (MetaArity T)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)}
    (hE : F.RespectsEquations E D) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ)
      {s : S.Srt} {t u : Term S Γ s}, EqClosure E t u →
      EqClosure D (mapTerm F ν t) (mapTerm F ν u)
  | _, _, ν, _, _, _, .ax i body ambient ordinary => by
      have mapped := eqClosure_bind
        (F.mapSub ν (fun _ v => Term.var v)) (hE i body ambient ordinary)
      simpa only [← F.map_bind, bind_id] using mapped
  | _, _, _, _, _, _, .refl _ => .refl _
  | _, _, ν, _, _, _, .symm h => .symm (F.eqClosure_map hE ν h)
  | _, _, ν, _, _, _, .trans h h' =>
      .trans (F.eqClosure_map hE ν h) (F.eqClosure_map hE ν h')
  | _, _, ν, _, _, _, .cong o h =>
      .cong (F.opMap o) (eqArgs_castArity (F.carriesArity o).symm
        (F.eqArgs_map hE ν h))

theorem SigMor.eqArgs_map (F : SigMor S T)
    {M : List (MetaArity S)} {N : List (MetaArity T)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)}
    (hE : F.RespectsEquations E D) :
    ∀ {Γ : Ctx S} {Δ : Ctx T} (ν : VarMap F.sortMap Γ Δ)
      {ars : List (List S.Srt × S.Srt)} {a b : Args S ars Γ},
      EqArgs E a b → EqArgs D (mapArgs F ν a) (mapArgs F ν b)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, ν, _, _, _, .cons (bs := bs) h ht =>
      .cons (F.eqClosure_map hE (liftVarMap F.sortMap ν bs) h)
        (F.eqArgs_map hE ν ht)
end

/-- The canonical action descends to equation classes. -/
theorem SigMor.eqClosure_onTerm (F : SigMor S T)
    {M : List (MetaArity S)} {N : List (MetaArity T)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)}
    (hE : F.RespectsEquations E D) {Γ : Ctx S} {s : S.Srt}
    {t u : Term S Γ s} (h : EqClosure E t u) :
    EqClosure D (F.onTerm t) (F.onTerm u) :=
  F.eqClosure_map hE (mapVar F.sortMap) h

/-- The induced function on the existing quotient, along a context map. -/
def SigMor.mapTermQ (F : SigMor S T)
    {M : List (MetaArity S)} {N : List (MetaArity T)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)}
    (hE : F.RespectsEquations E D) {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) {s : S.Srt} :
    TermQ E Γ s → TermQ D Δ (F.sortMap s) :=
  Quotient.map (mapTerm F ν) (fun _ _ h => F.eqClosure_map hE ν h)

/-- Substitution and translation commute on equivalence classes. -/
theorem SigMor.mapTermQ_bindQ (F : SigMor S T)
    {M : List (MetaArity S)} {N : List (MetaArity T)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)}
    (hE : F.RespectsEquations E D) {Γ Γ' : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ' Δ) (σ : Sub S Γ Γ') {s : S.Srt}
    (t : TermQ E Γ s) :
    F.mapTermQ hE ν (bindQ σ t) =
      bindQ (F.mapSub ν σ) (F.mapTermQ hE (mapVar F.sortMap) t) := by
  induction t using Quotient.inductionOn with
  | h t => exact congrArg (Quotient.mk _) (F.map_bind ν σ t)

/-- Translate an already translated context directly into the composite
context, retaining each variable's position even when sorts collapse. -/
def mapVarAfter {A B C : Type} (f : A → B) (g : B → C) :
    {Γ : List A} → VarMap g (Γ.map f) (Γ.map (fun s => g (f s)))
  | [], _, x => nomatch x
  | _ :: _, _, .zero => .zero
  | _ :: _, _, .succ x => .succ (mapVarAfter f g _ x)

theorem mapVarAfter_mapVar {A B C : Type} (f : A → B) (g : B → C) :
    ∀ {Γ : List A} (s : A) (x : Var Γ s),
      mapVarAfter f g (f s) (mapVar f s x) = mapVar (fun r => g (f r)) s x
  | _ :: _, _, .zero => rfl
  | _ :: _, _, .succ x => congrArg Var.succ (mapVarAfter_mapVar f g _ x)

theorem SigMor.mapTerm_after_onTerm {U : Signature} (F : SigMor S T) (G : SigMor T U)
    {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s) :
    mapTerm G (mapVarAfter F.sortMap G.sortMap) (F.onTerm t) = (F.comp G).onTerm t := by
  rw [SigMor.onTerm, mapTerm_comp]
  exact mapTerm_congr _ _ _ (mapVarAfter_mapVar F.sortMap G.sortMap) t

/-- Identity respects the same generators by their own axiom instances. -/
theorem SigMor.respectsEquations_ident {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) : (SigMor.ident S).RespectsEquations E E := by
  intro i Θ Γ body ambient ordinary
  have h := EqClosure.ax (E := E) i body ambient ordinary
  simpa only [SigMor.onTerm, mapTerm_ident] using
    eqClosure_rename (mapVar (fun s : S.Srt => s)) h

/-- Generator compatibility composes; callers supply no new closure law. -/
theorem SigMor.RespectsEquations.comp {U : Signature} {F : SigMor S T} {G : SigMor T U}
    {M : List (MetaArity S)} {N : List (MetaArity T)} {O : List (MetaArity U)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)} {H : List (EqAxiom U O)}
    (hF : F.RespectsEquations E D) (hG : G.RespectsEquations D H) :
    (F.comp G).RespectsEquations E H := by
  intro i Θ Γ body ambient ordinary
  have h := G.eqClosure_map hG (mapVarAfter F.sortMap G.sortMap)
    (hF i body ambient ordinary)
  simpa only [SigMor.mapTerm_after_onTerm] using h

/-- The descended maps compose with the existing term action. -/
theorem SigMor.mapTermQ_comp {U : Signature} (F : SigMor S T) (G : SigMor T U)
    {M : List (MetaArity S)} {N : List (MetaArity T)} {O : List (MetaArity U)}
    {E : List (EqAxiom S M)} {D : List (EqAxiom T N)} {H : List (EqAxiom U O)}
    (hF : F.RespectsEquations E D) (hG : G.RespectsEquations D H)
    {Γ : Ctx S} {Δ : Ctx T} {Θ : Ctx U}
    (ν : VarMap F.sortMap Γ Δ) (ν' : VarMap G.sortMap Δ Θ)
    {s : S.Srt} (t : TermQ E Γ s) :
    G.mapTermQ hG ν' (F.mapTermQ hF ν t) =
      (F.comp G).mapTermQ (hF.comp hG) (fun r x => ν' (F.sortMap r) (ν r x)) t := by
  induction t using Quotient.inductionOn with
  | h t => exact congrArg (Quotient.mk _) (mapTerm_comp F G ν ν' t)

/-- The descended identity is the identity on the existing quotient. -/
theorem SigMor.mapTermQ_ident {M : List (MetaArity S)}
    (E : List (EqAxiom S M)) {Γ : Ctx S} {s : S.Srt} (t : TermQ E Γ s) :
    (SigMor.ident S).mapTermQ (SigMor.respectsEquations_ident E) (fun _ x => x) t = t := by
  induction t using Quotient.inductionOn with
  | h t =>
      change Quotient.mk _ (mapTerm (SigMor.ident S) (fun _ x => x) t) = Quotient.mk _ t
      rw [mapTerm_ident, rename_id]

/-! With no generating equations, congruence creates no new equalities. -/

mutual
theorem eqClosure_empty_eq {M : List (MetaArity S)} :
    ∀ {Γ : Ctx S} {s : S.Srt} {t u : Term S Γ s},
      EqClosure ([] : List (EqAxiom S M)) t u → t = u
  | _, _, _, _, .ax i _ _ _ => Fin.elim0 i
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (eqClosure_empty_eq h).symm
  | _, _, _, _, .trans h h' => (eqClosure_empty_eq h).trans (eqClosure_empty_eq h')
  | _, _, _, _, .cong _ h => congrArg _ (eqArgs_empty_eq h)

theorem eqArgs_empty_eq {M : List (MetaArity S)} :
    ∀ {Γ : Ctx S} {ars : List (List S.Srt × S.Srt)} {a b : Args S ars Γ},
      EqArgs ([] : List (EqAxiom S M)) a b → a = b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons h ht => congrArg₂ Args.cons (eqClosure_empty_eq h) (eqArgs_empty_eq ht)
end

namespace EquationTransportControls

open ConstantMerge

/-- An authored equality between distinct constants. -/
def constantEquation : EqAxiom twoSig [] where
  ctx := []
  sort := ()
  lhs := .op (.inl .a) .nil
  rhs := .op (.inl .b) .nil

def constantTheory : List (EqAxiom twoSig []) := [constantEquation]

private def noBody : (k : Fin ([] : List (MetaArity twoSig)).length) →
    Term twoSig (([] : List (MetaArity twoSig)).get k).1
      (([] : List (MetaArity twoSig)).get k).2 := fun k => k.elim0

theorem constants_equated_at {Γ : Ctx twoSig} :
    EqClosure constantTheory (.op .a .nil : Term twoSig Γ ()) (.op .b .nil) := by
  have h := EqClosure.ax_closed (E := constantTheory) (Γ := Γ) ⟨0, by decide⟩ noBody
    (fun _ x => nomatch x)
  exact h

theorem constants_equated : EqClosure constantTheory ta tb := constants_equated_at

/-- A nonidentity map exchanges the two constant symbols. -/
def swap : SigMor twoSig twoSig where
  sortMap := id
  opMap := fun o => match o with
    | .a => .b
    | .b => .a
  carriesArity := fun o => by cases o <;> rfl

theorem swap_changes_term : swap.onTerm ta ≠ ta := by
  change tb ≠ ta
  exact Ne.symm ta_ne_tb

/-- The generator is carried to a genuinely derived equation: its symmetry. -/
theorem swap_respects : swap.RespectsEquations constantTheory constantTheory := by
  intro i Θ Γ body ambient ordinary
  have hi : i = ⟨0, by decide⟩ := by
    apply Fin.ext
    change i.val = 0
    have hi := i.isLt
    change i.val < 1 at hi
    omega
  subst i
  change EqClosure constantTheory (.op .b .nil : Term twoSig (Γ.map swap.sortMap) ()) (.op .a .nil)
  exact EqClosure.symm constants_equated_at

theorem swapped_equation : EqClosure constantTheory (swap.onTerm ta) (swap.onTerm tb) :=
  swap.eqClosure_onTerm swap_respects constants_equated

/-- A collapsing morphism can discharge a source generator by reflexivity. -/
theorem merge_respects : merge.RespectsEquations constantTheory
    ([] : List (EqAxiom oneSig [])) := by
  intro i Θ Γ body ambient ordinary
  have hi : i = ⟨0, by decide⟩ := by
    apply Fin.ext
    change i.val = 0
    have hi := i.isLt
    change i.val < 1 at hi
    omega
  subst i
  exact EqClosure.refl _

/-- The generator obligation is necessary: omitting the target equation fails. -/
theorem swap_does_not_respect_empty :
    ¬ swap.RespectsEquations constantTheory ([] : List (EqAxiom twoSig [])) := by
  intro h
  have he := eqClosure_empty_eq (h ⟨0, by decide⟩ (Θ := []) (Γ := []) (fun i => i.elim0)
    (fun _ x => nomatch x) (fun _ x => nomatch x))
  exact ta_ne_tb he.symm

/-- Preservation does not imply reflection through an operator collapse. -/
theorem collapse_does_not_reflect :
    EqClosure ([] : List (EqAxiom oneSig [])) (merge.onTerm ta) (merge.onTerm tb) ∧
      ¬ EqClosure ([] : List (EqAxiom twoSig [])) ta tb :=
  ⟨.refl _, fun h => ta_ne_tb (eqClosure_empty_eq h)⟩

end EquationTransportControls

end Mettapedia.OSLF.Binding
