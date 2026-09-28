import Mettapedia.Languages.Agda.Adequacy.StaticEmbedding

/-!
# The supported image of raw static syntax

The decoder recognizes finite Set annotations, both abstraction forms, and
unreduced single applications. In particular, it accepts applications of
lambdas and rejects structural projection, empty elimination, multi-element
spines at one elimination node, and administrative append nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def decodeClosedLevel {Γ : Ctx sig} : Structural.Level Γ → Option Nat
  | .var _ => none
  | .op (.levelClosed value) .nil => some value
  | .op .levelSuc _ | .op .levelMax _ | .op .levelNeutral _ => none

def decodeFiniteSet {Γ : Ctx sig} : Structural.UnivSort Γ → Option Nat
  | .var _ => none
  | .op .set (.cons level .nil) => decodeClosedLevel level
  | .op .prop _ | .op (.setOmega _) _ => none

mutual
  def decodeTerm : {n : Nat} → Structural.Tm (scope n) → Option (StaticSpecification.Term n)
    | _, .var index => some (.var (readVar index))
    | n, .op .lam (.cons body .nil) =>
        (decodeTerm (n := n + 1) body).map (fun term => .lam (.bind term))
    | _, .op .lamNoAbs (.cons body .nil) =>
        (decodeTerm body).map (fun term => .lam (.noBind term))
    | n, .op .pi (.cons domain (.cons body .nil)) => do
        let domain ← decodeTy domain
        let body ← decodeTy (n := n + 1) body
        pure (.pi domain (.bind body))
    | _, .op .piNoAbs (.cons domain (.cons body .nil)) => do
        let domain ← decodeTy domain
        let body ← decodeTy body
        pure (.pi domain (.noBind body))
    | _, .op .sortTerm (.cons sort .nil) => (decodeFiniteSet sort).map .sort
    | _, .op .eliminate (.cons head (.cons spine .nil)) => do
        let head ← decodeTerm head
        let elimination ← decodeSingleton spine
        pure (.elim head elimination)
    | _, .op (.defined _) _ | _, .op (.constructor _) _
    | _, .op (.natLiteral _) _ | _, .op .levelTerm _ => none
  termination_by _ term => termSize term
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  def decodeTy : {n : Nat} → Structural.Ty (scope n) → Option (StaticSpecification.Ty n)
    | _, .var _ => none
    | _, .op .el (.cons sort (.cons term .nil)) => do
        let level ← decodeFiniteSet sort
        (decodeTerm term).map (.el level)
  termination_by _ ty => termSize ty
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  def decodeElim : {n : Nat} → Structural.Elim (scope n) → Option (StaticSpecification.Elim n)
    | _, .var _ => none
    | _, .op .apply (.cons term .nil) => (decodeTerm term).map .apply
    | _, .op (.proj _) _ => none
  termination_by _ elimination => termSize elimination
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  /-- One source elimination occupies one structural elimination node. -/
  def decodeSingleton : {n : Nat} → Structural.Spine (scope n) → Option (StaticSpecification.Elim n)
    | _, .op .cons (.cons head (.cons (.op .nil .nil) .nil)) => decodeElim head
    | _, .var _ | _, .op .nil _ | _, .op .append _ => none
    | _, .op .cons (.cons _ (.cons (.var _) .nil)) => none
    | _, .op .cons (.cons _ (.cons (.op .cons _) .nil)) => none
    | _, .op .cons (.cons _ (.cons (.op .append _) .nil)) => none
  termination_by _ spine => termSize spine
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)
end

def decodeSpine : {n : Nat} → Structural.Spine (scope n) → Option (StaticSpecification.Spine n)
  | _, .op .nil .nil => some []
  | _, .op .cons (.cons head (.cons rest .nil)) => do
      let head ← decodeElim head
      let rest ← decodeSpine rest
      pure (head :: rest)
  | _, .var _ | _, .op .append _ => none
termination_by _ spine => termSize spine
decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

mutual
  @[simp] theorem decodeTerm_embedTerm {n : Nat} (term : StaticSpecification.Term n) :
      decodeTerm (embedTerm term) = some term := by
    match term with
    | .var index =>
        rw [embedTerm, decodeTerm.eq_def]
        change some (StaticSpecification.Term.var (readVar (embedVar index))) = _
        rw [read_embedVar]
    | .lam (.bind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTerm (embedTerm body)).map (fun term => StaticSpecification.Term.lam (.bind term)) = _
        rw [decodeTerm_embedTerm]
        rfl
    | .lam (.noBind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTerm (embedTerm body)).map (fun term => StaticSpecification.Term.lam (.noBind term)) = _
        rw [decodeTerm_embedTerm]
        rfl
    | .pi domain (.bind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTy (embedTy domain)).bind (fun domain =>
          (decodeTy (embedTy body)).bind (fun body => some (StaticSpecification.Term.pi domain (.bind body)))) = _
        rw [decodeTy_embedTy, decodeTy_embedTy]
        rfl
    | .pi domain (.noBind body) =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTy (embedTy domain)).bind (fun domain =>
          (decodeTy (embedTy body)).bind (fun body => some (StaticSpecification.Term.pi domain (.noBind body)))) = _
        rw [decodeTy_embedTy, decodeTy_embedTy]
        rfl
    | .sort _ =>
        rw [embedTerm, decodeTerm.eq_def]
        rfl
    | .elim head elimination =>
        rw [embedTerm, decodeTerm.eq_def]
        change (decodeTerm (embedTerm head)).bind (fun head =>
          (decodeSingleton (Structural.cons (embedElim elimination) Structural.nil)).bind
            (fun elimination => some (StaticSpecification.Term.elim head elimination))) = _
        rw [decodeTerm_embedTerm, decodeSingleton.eq_def]
        change (decodeElim (embedElim elimination)).bind
          (fun elimination => some (StaticSpecification.Term.elim head elimination)) = _
        rw [decodeElim_embedElim]
        rfl

  @[simp] theorem decodeTy_embedTy {n : Nat} (ty : StaticSpecification.Ty n) :
      decodeTy (embedTy ty) = some ty := by
    match ty with
    | .el level term =>
        rw [embedTy, decodeTy.eq_def]
        change (decodeTerm (embedTerm term)).map (StaticSpecification.Ty.el level) = _
        rw [decodeTerm_embedTerm]
        rfl

  @[simp] theorem decodeElim_embedElim {n : Nat} (elimination : StaticSpecification.Elim n) :
      decodeElim (embedElim elimination) = some elimination := by
    match elimination with
    | .apply term =>
        rw [embedElim, decodeElim.eq_def]
        change (decodeTerm (embedTerm term)).map StaticSpecification.Elim.apply = _
        rw [decodeTerm_embedTerm]
        rfl
end

@[simp] theorem decodeSpine_embedSpine {n : Nat} (spine : StaticSpecification.Spine n) :
    decodeSpine (embedSpine spine) = some spine := by
  induction spine with
  | nil => rw [embedSpine, decodeSpine.eq_def]; rfl
  | cons e es ih =>
      rw [embedSpine, decodeSpine.eq_def]
      change (decodeElim (embedElim e)).bind (fun e =>
        (decodeSpine (embedSpine es)).bind (fun es => some (e :: es))) = _
      rw [decodeElim_embedElim, ih]
      rfl

theorem embedTerm_injective {n : Nat} : Function.Injective (embedTerm (n := n)) := by
  intro first second same
  have decoded := congrArg decodeTerm same
  simpa only [decodeTerm_embedTerm, Option.some.injEq] using decoded

theorem embedTy_injective {n : Nat} : Function.Injective (embedTy (n := n)) := by
  intro first second same
  have decoded := congrArg decodeTy same
  simpa only [decodeTy_embedTy, Option.some.injEq] using decoded

theorem embedElim_injective {n : Nat} : Function.Injective (embedElim (n := n)) := by
  intro first second same
  have decoded := congrArg decodeElim same
  simpa only [decodeElim_embedElim, Option.some.injEq] using decoded

theorem embedSpine_injective {n : Nat} : Function.Injective (embedSpine (n := n)) := by
  intro first second same
  have decoded := congrArg decodeSpine same
  simpa only [decodeSpine_embedSpine, Option.some.injEq] using decoded

theorem levelClosed_of_decode {Γ : Ctx sig} (level : Structural.Level Γ)
    {value : Nat} (decoded : decodeClosedLevel level = some value) :
    Structural.levelClosed value = level := by
  match level with
  | .var _ => cases decoded
  | .op (.levelClosed value') .nil => cases decoded; rfl
  | .op .levelSuc _ | .op .levelMax _ | .op .levelNeutral _ => cases decoded

theorem finiteSet_of_decode {Γ : Ctx sig} (sort : Structural.UnivSort Γ)
    {value : Nat} (decoded : decodeFiniteSet sort = some value) :
    Structural.set (Structural.levelClosed value) = sort := by
  match sort with
  | .var _ => cases decoded
  | .op .set (.cons level .nil) =>
      exact congrArg Structural.set (levelClosed_of_decode level decoded)
  | .op .prop _ | .op (.setOmega _) _ => cases decoded

mutual
  /-- Every successful parse reconstructs the original structural term exactly. -/
  theorem embedTerm_of_decode {n : Nat} (term : Structural.Tm (scope n))
      {source : StaticSpecification.Term n} (decoded : decodeTerm term = some source) :
      embedTerm source = term := by
    match term with
    | .var index =>
        rw [decodeTerm.eq_def] at decoded
        change some (StaticSpecification.Term.var (readVar index)) = some source at decoded
        cases Option.some.inj decoded
        exact congrArg Term.var (embed_readVar index)
    | .op .lam (.cons body .nil) =>
        rw [decodeTerm.eq_def] at decoded
        change (decodeTerm (n := n + 1) body).map
          (fun term => StaticSpecification.Term.lam (.bind term)) = some source at decoded
        obtain ⟨body', parsed, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Structural.lam (embedTerm_of_decode (n := n + 1) body parsed)
    | .op .lamNoAbs (.cons body .nil) =>
        rw [decodeTerm.eq_def] at decoded
        change (decodeTerm body).map
          (fun term => StaticSpecification.Term.lam (.noBind term)) = some source at decoded
        obtain ⟨body', parsed, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Structural.lamNoAbs (embedTerm_of_decode body parsed)
    | .op .pi (.cons domain (.cons body .nil)) =>
        rw [decodeTerm.eq_def] at decoded
        change (decodeTy domain).bind (fun domain =>
          (decodeTy (n := n + 1) body).bind
            (fun body => some (StaticSpecification.Term.pi domain (.bind body)))) = some source at decoded
        obtain ⟨domain', parsedDomain, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨body', parsedBody, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        cases Option.some.inj decoded
        exact congrArg₂ Structural.pi
          (embedTy_of_decode domain parsedDomain) (embedTy_of_decode (n := n + 1) body parsedBody)
    | .op .piNoAbs (.cons domain (.cons body .nil)) =>
        rw [decodeTerm.eq_def] at decoded
        change (decodeTy domain).bind (fun domain =>
          (decodeTy body).bind
            (fun body => some (StaticSpecification.Term.pi domain (.noBind body)))) = some source at decoded
        obtain ⟨domain', parsedDomain, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨body', parsedBody, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        cases Option.some.inj decoded
        exact congrArg₂ Structural.piNoAbs
          (embedTy_of_decode domain parsedDomain) (embedTy_of_decode body parsedBody)
    | .op .sortTerm (.cons sort .nil) =>
        rw [decodeTerm.eq_def] at decoded
        change (decodeFiniteSet sort).map StaticSpecification.Term.sort = some source at decoded
        obtain ⟨value, parsed, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Structural.sortTerm (finiteSet_of_decode sort parsed)
    | .op .eliminate (.cons head (.cons spine .nil)) =>
        rw [decodeTerm.eq_def] at decoded
        change (decodeTerm head).bind (fun head =>
          (decodeSingleton spine).bind (fun elimination =>
            some (StaticSpecification.Term.elim head elimination))) = some source at decoded
        obtain ⟨head', parsedHead, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨elimination, parsedElimination, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        cases Option.some.inj decoded
        exact congrArg₂ Structural.eliminate
          (embedTerm_of_decode head parsedHead) (embedSingleton_of_decode spine parsedElimination)
    | .op (.defined _) _ | .op (.constructor _) _
    | .op (.natLiteral _) _ | .op .levelTerm _ =>
        rw [decodeTerm.eq_def] at decoded
        cases decoded
  termination_by termSize term
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  theorem embedTy_of_decode {n : Nat} (ty : Structural.Ty (scope n))
      {source : StaticSpecification.Ty n} (decoded : decodeTy ty = some source) :
      embedTy source = ty := by
    match ty with
    | .var _ => rw [decodeTy.eq_def] at decoded; cases decoded
    | .op .el (.cons sort (.cons term .nil)) =>
        rw [decodeTy.eq_def] at decoded
        change (decodeFiniteSet sort).bind (fun level =>
          (decodeTerm term).map (StaticSpecification.Ty.el level)) = some source at decoded
        obtain ⟨value, parsedSort, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨term', parsedTerm, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg₂ Structural.el
          (finiteSet_of_decode sort parsedSort) (embedTerm_of_decode term parsedTerm)
  termination_by termSize ty
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  theorem embedElim_of_decode {n : Nat} (elimination : Structural.Elim (scope n))
      {source : StaticSpecification.Elim n} (decoded : decodeElim elimination = some source) :
      embedElim source = elimination := by
    match elimination with
    | .var _ | .op (.proj _) _ => rw [decodeElim.eq_def] at decoded; cases decoded
    | .op .apply (.cons term .nil) =>
        rw [decodeElim.eq_def] at decoded
        change (decodeTerm term).map StaticSpecification.Elim.apply = some source at decoded
        obtain ⟨term', parsedTerm, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg Structural.apply (embedTerm_of_decode term parsedTerm)
  termination_by termSize elimination
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

  theorem embedSingleton_of_decode {n : Nat} (spine : Structural.Spine (scope n))
      {source : StaticSpecification.Elim n} (decoded : decodeSingleton spine = some source) :
      Structural.cons (embedElim source) Structural.nil = spine := by
    match spine with
    | .op .cons (.cons head (.cons (.op .nil .nil) .nil)) =>
        rw [decodeSingleton.eq_def] at decoded
        exact congrArg (fun e => Structural.cons e Structural.nil) (embedElim_of_decode head decoded)
    | .var _ | .op .nil _ | .op .append _
    | .op .cons (.cons _ (.cons (.var _) .nil))
    | .op .cons (.cons _ (.cons (.op .cons _) .nil))
    | .op .cons (.cons _ (.cons (.op .append _) .nil)) =>
        rw [decodeSingleton.eq_def] at decoded
        cases decoded
  termination_by termSize spine
  decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)
end

theorem embedSpine_of_decode {n : Nat} (spine : Structural.Spine (scope n))
    {source : StaticSpecification.Spine n} (decoded : decodeSpine spine = some source) :
    embedSpine source = spine := by
  match spine with
  | .op .nil .nil =>
      rw [decodeSpine.eq_def] at decoded
      cases Option.some.inj decoded
      rfl
  | .op .cons (.cons head (.cons rest .nil)) =>
      rw [decodeSpine.eq_def] at decoded
      change (decodeElim head).bind (fun head =>
        (decodeSpine rest).bind (fun rest => some (head :: rest))) = some source at decoded
      obtain ⟨head', parsedHead, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨rest', parsedRest, decoded⟩ := Option.bind_eq_some_iff.mp decoded
      cases Option.some.inj decoded
      exact congrArg₂ Structural.cons
        (embedElim_of_decode head parsedHead) (embedSpine_of_decode rest parsedRest)
  | .var _ | .op .append _ => rw [decodeSpine.eq_def] at decoded; cases decoded
termination_by termSize spine
decreasing_by all_goals (simp only [termSize, argsSize, scope]; omega)

theorem decodeTerm_eq_some_iff {n : Nat} (term : Structural.Tm (scope n))
    (source : StaticSpecification.Term n) :
    decodeTerm term = some source ↔ embedTerm source = term := by
  constructor
  · exact embedTerm_of_decode term
  · intro same; rw [← same, decodeTerm_embedTerm]

theorem decodeTy_eq_some_iff {n : Nat} (ty : Structural.Ty (scope n))
    (source : StaticSpecification.Ty n) :
    decodeTy ty = some source ↔ embedTy source = ty := by
  constructor
  · exact embedTy_of_decode ty
  · intro same; rw [← same, decodeTy_embedTy]

theorem decodeElim_eq_some_iff {n : Nat} (elimination : Structural.Elim (scope n))
    (source : StaticSpecification.Elim n) :
    decodeElim elimination = some source ↔ embedElim source = elimination := by
  constructor
  · exact embedElim_of_decode elimination
  · intro same; rw [← same, decodeElim_embedElim]

theorem decodeSpine_eq_some_iff {n : Nat} (spine : Structural.Spine (scope n))
    (source : StaticSpecification.Spine n) :
    decodeSpine spine = some source ↔ embedSpine source = spine := by
  constructor
  · exact embedSpine_of_decode spine
  · intro same; rw [← same, decodeSpine_embedSpine]

theorem decode_rejects_projection {n : Nat} (name : String) :
    decodeElim (Structural.proj (Γ := scope n) name) = none := by
  rw [decodeElim.eq_def]
  rfl

theorem decode_rejects_empty_elimination {n : Nat} (head : Structural.Tm (scope n)) :
    decodeTerm (Structural.eliminate head Structural.nil) = none := by
  rw [decodeTerm.eq_def]
  change (decodeTerm head).bind (fun head => (decodeSingleton Structural.nil).bind
    (fun elimination => some (StaticSpecification.Term.elim head elimination))) = none
  rw [decodeSingleton.eq_def]
  cases decodeTerm head <;> rfl

theorem decode_rejects_multiple_elimination {n : Nat} (head : Structural.Tm (scope n))
    (first second : Structural.Elim (scope n)) (rest : Structural.Spine (scope n)) :
    decodeTerm (Structural.eliminate head (Structural.cons first (Structural.cons second rest))) = none := by
  rw [decodeTerm.eq_def]
  change (decodeTerm head).bind (fun head =>
    (decodeSingleton (Structural.cons first (Structural.cons second rest))).bind
      (fun elimination => some (StaticSpecification.Term.elim head elimination))) = none
  rw [decodeSingleton.eq_def]
  cases decodeTerm head <;> rfl

theorem decode_rejects_append {n : Nat} (first second : Structural.Spine (scope n)) :
    decodeSpine (Structural.append first second) = none := by
  rw [decodeSpine.eq_def]
  rfl

theorem decode_rejects_prop_annotation {n : Nat} (level : Structural.Level (scope n))
    (term : Structural.Tm (scope n)) :
    decodeTy (Structural.el (Structural.prop level) term) = none := by
  rw [decodeTy.eq_def]
  rfl

end Mettapedia.Languages.Agda.StaticAdequacy
