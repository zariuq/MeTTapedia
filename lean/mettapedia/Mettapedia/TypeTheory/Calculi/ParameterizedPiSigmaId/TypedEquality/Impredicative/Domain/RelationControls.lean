import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Relation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.InterpControls

/-!
# Controls for the witness-indexed relation

* **η for pairs, positive.** At `Σ A B → Σ A B`, for every dependent pair type
  `Σ A B` whose only facet is `Σ`, the identity `λp. p` and its η-expansion
  `λp. (p.1, p.2)` are related (`eta_related`). Their interpretations differ as
  ideals (`InterpControls.eta_not_equal_interp`); the relation compares pairs by
  components, so it relates them by definition of the clause at `Σ`
  (`eta_component`).
* **Application, negative.** At the type of type families `U → U`, the identity
  and the constant family with value the numbers are not related: the identity
  sends a dependent function type to a dependent function type, and the
  constant sends it to the numbers (`not_related_id_constant`). So the relation
  is not trivial at function types.
* **Impredicativity.** The universe of codes is interpreted by the tag `codes`,
  decoding is the identity on codes, and the code of `∀ P : Prop. P → P` then
  denotes `Π P : Prop. Π _ : P. P`. The relation at the universe of codes is
  well defined although the quantified codes `P` range over all codes, including
  this one: each is observed through a smaller witness. The code is related to
  itself at the universe of codes (`allCode_related`), and the polymorphic
  identity `λP. λp. p` is related to itself at it (`polyId_related`): its
  instances at every two codes observed alike are related.
* **Declared datatypes and constructors, positive and negative.** At the lists of
  numbers, the empty list is related to itself as far as its tag observes
  (`nil_related`), and it is not related to a non-empty list: two different
  constructors (`nil_cons_unrelated`). One-element lists are related as far as the
  token saying that the tail is empty observes (`single_tail_related`), and `[a]` and
  `[a, b]`, whose tails are not related there, are not (`single_pair_unrelated`).
  Closure under entailment needs the field tokens: the tag of `cons` relates `[a]` and
  `[a, b]`, and the tag with the field token entails the field token, which does not
  (`closed_needs_fields`). As types, the lists of numbers are related to themselves at
  the token saying that the parameter is the numbers (`listNat_param_related`), and
  not to the lists of lists of numbers (`listNat_listList_unrelated`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace RelationControls

open Ideal InterpControls

/-! ## η for pairs -/

section Eta

variable {S : Ideal} (hpi : ¬ S.Mem (.tag .pi)) (hd : ∀ d, ¬ S.Mem (.tag (.data d)))
  (hU : ¬ IsUnivI S) (hs : S.Mem (.tag .sigma))
include hpi hd hU hs

/-- An element is related to the η-expansion of an element it is related to. -/
theorem eta_component {u : List Tok} {y y' : Ideal} (h : Rel S u y y') :
    Rel S u y (Ideal.pair (Ideal.fst y') (Ideal.snd y')) := by
  refine Rel.of_components hpi hd hU ?_ ?_
  · rw [fst_pair]; exact h.fst hs
  · rw [snd_pair]; exact h.snd hs

/-- **η for pairs**: the identity and `λp. (p.1, p.2)` are related at `S → S`. -/
theorem eta_related :
    Sem (former .pi S fun _ => S) (interp unitReading idFun emptyEnv)
      (interp unitReading etaPairFun emptyEnv) := by
  have hTs : ¬ (former .pi S fun _ => S).Mem (.tag .sigma) := fun h =>
    absurd (former_mem_tag_iff.1 h) (by decide)
  have hTd : ∀ d, ¬ (former .pi S fun _ => S).Mem (.tag (.data d)) := fun _ h =>
    absurd (former_mem_tag_iff.1 h) nofun
  have hTU : ¬ IsUnivI (former .pi S fun _ => S) := by
    rintro (h | h)
    · exact absurd (former_mem_tag_iff.1 h) (by decide)
    · exact absurd (former_mem_tag_iff.1 h) (by decide)
  intro u hu t ht
  cases t with
  | tag k => exact RT.of_not_lam hTs hTd hTU fun _ _ _ e => nomatch e
  | arg k i C s => exact RT.of_not_lam hTs hTd hTU fun _ _ _ e => nomatch e
  | fn k C Z Y =>
    by_cases hk : k = .lam
    · subst hk
      refine RT.lam_iff.2 ⟨fun _ y y' hZ s hsY => ?_, fun h => absurd h hTU⟩
      rw [dom_former] at hZ
      rw [fam_former_const, idFun, etaPairFun, app_interp_lam, app_interp_lam]
      show RT true s S y (Ideal.pair (Ideal.fst y') (Ideal.snd y'))
      have hY : Ideal.Below Y (principal Z) :=
        below_of_mem_lam (interp_family_monotone unitReading (.var 0) emptyEnv) (hu _ ht)
      exact eta_component hpi hd hU hs (Rel.mono (T := S) hZ fun r hr => hY r hr) s hsY
    · exact RT.of_not_lam hTs hTd hTU fun _ _ _ e => hk (Tok.fn.inj e).1

end Eta

/-! ## Application, negative -/

/-- A reading whose heads denote the numbers. -/
def natReading : Reading Unit where
  head := fun _ => Elem.nat
  const := fun _ => bot

/-- The constant family with value the numbers. -/
def constNat : Tm Unit 0 := .lam (.head ())

/-- The universe, as an ideal. -/
def univI : Ideal := principal Elem.univ

theorem univI_isUniv : IsUnivI univI := .inl (ent_of_mem List.mem_cons_self)

/-- The identity and the constant family with value the numbers are not related
at `U → U`. -/
theorem not_related_id_constant :
    ¬ Sem (former .pi univI fun _ => univI) (interp natReading idFun emptyEnv)
      (interp natReading constNat emptyEnv) := by
  intro h
  let w : List Tok := [.tag .pi]
  have hmem : (interp natReading idFun emptyEnv).Mem (.fn .lam [] w w) := by
    refine (mem_lam_fn (interp_family_monotone natReading (.var 0) emptyEnv)).2 ?_
    intro s hs
    exact ent_of_mem hs
  have hrel := h [.fn .lam [] w w] (fun s hs => by rw [List.mem_singleton.1 hs]; exact hmem)
    (.fn .lam [] w w) List.mem_cons_self
  have hin : ∀ s ∈ w, RT true s (dom .pi (former .pi univI fun _ => univI)) (principal w)
      (principal w) := by
    intro s hs
    rw [List.mem_singleton.1 hs, dom_former]
    exact (RT.tag_iff (k := .pi) fun _ _ _ e => nomatch e).2 fun _ => RT.ty_tag_iff.2 fun _ =>
      ⟨ent_of_mem List.mem_cons_self, ent_of_mem List.mem_cons_self⟩
  have hout := (RT.lam_iff.1 hrel).1 (mem_former_tag _ _ _) (principal w) (principal w) hin
    (.tag .pi) List.mem_cons_self
  rw [fam_former_const, idFun, constNat, app_interp_lam, app_interp_lam] at hout
  have hty := (RT.ty_tag_iff.1 (RT.univ hout univI_isUniv) trivial).2
  change ent Elem.nat (.tag .pi) = true at hty
  simp [Elem.nat, ent_tag, hasTag] at hty

/-! ## Impredicativity -/

/-- A reading whose declared constants denote the universe of codes. -/
def codesReading : Reading Unit where
  head := fun _ => []
  const := fun _ => principal Elem.codes

/-- The universe of codes. -/
def propI : Ideal := principal Elem.codes

/-- The type of codes, as a term. -/
def propT {n : Nat} : Tm Unit n := .const `prop

/-- The decoding of the code of `∀ P : Prop. P → P`: `Π P : Prop. Π _ : P. P`. -/
def allCode : Tm Unit 0 := .pi propT (.pi (.var 0) (.var 1))

/-- The polymorphic identity `λP. λp. p`. -/
def polyId : Tm Unit 0 := .lam (.lam (.var 0))

theorem propI_isUniv : IsUnivI propI := .inr (ent_of_mem List.mem_cons_self)

theorem propI_not_pi : ¬ propI.Mem (.tag .pi) := by
  intro h
  change ent Elem.codes (.tag .pi) = true at h
  simp [Elem.codes, ent_tag, hasTag] at h

theorem propI_not_sigma : ¬ propI.Mem (.tag .sigma) := by
  intro h
  change ent Elem.codes (.tag .sigma) = true at h
  simp [Elem.codes, ent_tag, hasTag] at h

theorem propI_not_data (d : DeclName) : ¬ propI.Mem (.tag (.data d)) := by
  intro h
  change ent Elem.codes (.tag (.data d)) = true at h
  simp [Elem.codes, ent_tag, hasTag] at h

/-- Every token of the universe of codes relates it to itself. -/
theorem propI_self {d : Tok} (hd : propI.Mem d) : RT false d bot propI propI := by
  refine RT.closed false Elem.codes d bot propI propI hd fun s hs => ?_
  rw [List.mem_singleton.1 hs]
  exact RT.ty_tag_iff.2 fun _ => ⟨ent_of_mem List.mem_cons_self, ent_of_mem List.mem_cons_self⟩

/-- The body `Π _ : P. P`, with `y` for `P`. -/
abbrev body (y : Ideal) : Ideal := interp codesReading (.pi (.var 0) (.var 1)) (Env.cons y emptyEnv)

theorem dom_body (y : Ideal) : dom .pi (body y) = y := dom_interp_pi _ _ _ _

theorem fam_body (y z : Ideal) : fam .pi (body y) z = y := fam_interp_pi _ _ _ _ _

/-- `Π _ : P. P` at the codes observed by `Z` is related to itself at any two codes
related as far as `Z` observes. -/
theorem body_related {Z : List Tok} {y y' : Ideal} (hZ : TyRel Z y y') {s : Tok}
    (hs : (body (principal Z)).Mem s) : RT false s bot (body y) (body y') := by
  refine RT.of_mem_closure (fun g hg => ?_) hs
  rcases hg with rfl | ⟨d, rfl, hd⟩ | ⟨D, Z', W, rfl, hD, hW⟩
  · exact RT.ty_tag_iff.2 fun _ => ⟨mem_former_tag _ _ _, mem_former_tag _ _ _⟩
  · refine RT.ty_arg_iff.2 ⟨fun _ => ⟨fun c hc => absurd hc List.not_mem_nil, fun _ => ?_⟩,
      fun _ e => nomatch e⟩
    rw [dom_body, dom_body]
    exact RT.closed false Z d bot y y' hd hZ
  · refine RT.ty_fn_iff.2 ⟨fun _ => ⟨fun c hc => ?_, fun v v' _ s' hs' => ?_⟩, fun _ e => nomatch e⟩
    · rw [dom_body, dom_body]
      exact RT.closed false Z c bot y y' (hD c hc) hZ
    · rw [fam_body, fam_body]
      exact RT.closed false Z s' bot y y' (hW s' hs') hZ

/-- **The impredicative control**: the code of `∀ P : Prop. P → P` is related to
itself as a type, as far as any of its witnesses observes. -/
theorem allCode_selfTy : STy (interp codesReading allCode emptyEnv)
    (interp codesReading allCode emptyEnv) := by
  intro u hu t ht
  refine RT.of_mem_closure (fun g hg => ?_) (hu t ht)
  rcases hg with rfl | ⟨d, rfl, hd⟩ | ⟨D, Z, W, rfl, hD, hW⟩
  · exact RT.ty_tag_iff.2 fun _ => ⟨mem_former_tag _ _ _, mem_former_tag _ _ _⟩
  · refine RT.ty_arg_iff.2 ⟨fun _ => ⟨fun c hc => absurd hc List.not_mem_nil, fun _ => ?_⟩,
      fun _ e => nomatch e⟩
    rw [allCode, dom_interp_pi]
    exact propI_self hd
  · refine RT.ty_fn_iff.2 ⟨fun _ => ⟨fun c hc => ?_, fun y y' hZ s hs => ?_⟩, fun _ e => nomatch e⟩
    · rw [allCode, dom_interp_pi]
      exact propI_self (hD c hc)
    · rw [allCode, dom_interp_pi] at hZ
      rw [allCode, fam_interp_pi, fam_interp_pi]
      exact body_related (fun r hr => RT.univ (hZ r hr) propI_isUniv) (hW s hs)

/-- **The impredicative control, at the universe of codes**: the code of
`∀ P : Prop. P → P` is related to itself at `Prop`. -/
theorem allCode_related : Sem propI (interp codesReading allCode emptyEnv)
    (interp codesReading allCode emptyEnv) :=
  fun u hu t ht => RT.of_univ propI_not_pi propI_not_sigma propI_not_data fun _ =>
    allCode_selfTy u hu t ht

/-- The identity is related to itself at `Π _ : P. P`, for every `P`. -/
theorem id_related_body (y : Ideal) :
    Sem (body y) (interp codesReading idFun emptyEnv) (interp codesReading idFun emptyEnv) := by
  have hbs : ¬ (body y).Mem (.tag .sigma) := fun h => absurd (former_mem_tag_iff.1 h) (by decide)
  have hbU : ¬ IsUnivI (body y) := by
    rintro (h | h)
    · exact absurd (former_mem_tag_iff.1 h) (by decide)
    · exact absurd (former_mem_tag_iff.1 h) (by decide)
  intro u hu t ht
  refine RT.of_mem_closure (fun g hg => ?_) (hu t ht)
  obtain ⟨Z, Y, rfl, hY⟩ := hg
  refine RT.lam_iff.2 ⟨fun _ z z' hZ s hs => ?_, fun h => absurd h hbU⟩
  rw [dom_body] at hZ
  rw [fam_body, idFun, app_interp_lam, app_interp_lam]
  have hYZ : Y ⊑ Z := fun r hr => hY r hr
  exact (Rel.mono (T := y) hZ hYZ) s hs

/-- **The polymorphic identity at an impredicative type**: `λP. λp. p` is related
to itself at `Π P : Prop. Π _ : P. P`. Its instances at every two codes, the
code of this type included, are related. -/
theorem polyId_related : Sem (interp codesReading allCode emptyEnv)
    (interp codesReading polyId emptyEnv) (interp codesReading polyId emptyEnv) := by
  have hTs : ¬ (interp codesReading allCode emptyEnv).Mem (.tag .sigma) := fun h =>
    absurd (former_mem_tag_iff.1 h) (by decide)
  have hTU : ¬ IsUnivI (interp codesReading allCode emptyEnv) := by
    rintro (h | h)
    · exact absurd (former_mem_tag_iff.1 h) (by decide)
    · exact absurd (former_mem_tag_iff.1 h) (by decide)
  intro u hu t ht
  refine RT.of_mem_closure (fun g hg => ?_) (hu t ht)
  obtain ⟨Z, Y, rfl, hY⟩ := hg
  refine RT.lam_iff.2 ⟨fun _ y y' _ s hs => ?_, fun h => absurd h hTU⟩
  rw [allCode, fam_interp_pi, polyId, app_interp_lam, app_interp_lam]
  exact id_related_body y [s] (fun r hr => by rw [List.mem_singleton.1 hr]; exact hY s hs) s
    List.mem_cons_self

/-! ## Declared datatypes and constructors -/

section Declared

local notation "listK" => Kind.data `list
local notation "nilK" => Kind.ctor `list `nil []
local notation "consK" => Kind.ctor `list `cons [FieldShape.param 0, FieldShape.self]
local notation "listNatI" => ctorI listK [natI]

theorem listNatI_mem : (listNatI).Mem (.tag listK) := ctorI_mem_tag _ _

theorem natI_mem_nat : natI.Mem (.tag .nat) := mem_principal_tag.2 rfl

theorem listNatI_not_univ : ¬ IsUnivI listNatI := by
  rintro (h | h) <;> exact absurd (ctorI_mem_tag_iff.1 h) nofun

/-- **Positive**: the lists of numbers are related to themselves as types, as far as the token
saying that their parameter is the numbers observes. -/
theorem listNat_param_related :
    RT false (.arg listK 0 [] (.tag .nat)) bot listNatI listNatI := by
  refine RT.ty_arg_iff.2 ⟨fun h => by rcases h with h | h <;> exact absurd h nofun,
    fun d hd => ⟨fun c hc => absurd hc List.not_mem_nil, ?_⟩⟩
  rw [fieldI_ctorI]
  exact RT.ty_tag_iff.2 fun _ => ⟨natI_mem_nat, natI_mem_nat⟩

/-- **Negative**: the lists of numbers and the lists of lists of numbers are not related as
types, as far as the token saying that the parameter is the numbers observes. -/
theorem listNat_listList_unrelated :
    ¬ RT false (.arg listK 0 [] (.tag .nat)) bot listNatI (ctorI listK [listNatI]) := by
  intro h
  have h₀ := ((RT.ty_arg_iff.1 h).2 _ rfl).2
  rw [fieldI_ctorI, fieldI_ctorI] at h₀
  exact absurd (ctorI_mem_tag_iff.1 ((RT.ty_tag_iff.1 h₀ trivial).2)) nofun

/-- **Positive**: the empty list is related to itself, as far as its tag observes. -/
theorem nil_related : RT true (.tag nilK) listNatI (ctorI nilK []) (ctorI nilK []) :=
  RT.ctorTag_iff.2 ⟨fun _ => ⟨ctorI_mem_tag _ _, ctorI_mem_tag _ _⟩,
    fun h => absurd h listNatI_not_univ⟩

/-- **Negative**: two different constructors are not related: the empty list and a non-empty
one, as far as the tag of the empty list observes. -/
theorem nil_cons_unrelated (a l : Ideal) :
    ¬ RT true (.tag nilK) listNatI (ctorI nilK []) (ctorI consK [a, l]) := by
  intro h
  exact absurd (ctorI_mem_tag_iff.1 ((RT.ctorTag_iff.1 h).1 listNatI_mem).2) (by decide)

/-- **Positive**: one-element lists are related, as far as the token saying that the tail is the
empty list observes. -/
theorem single_tail_related (a a' : Ideal) :
    RT true (.arg consK 1 [] (.tag nilK)) listNatI (ctorI consK [a, ctorI nilK []])
      (ctorI consK [a', ctorI nilK []]) := by
  refine RT.ctorArg_iff.2 ⟨fun _ => ⟨fun r hr => absurd hr List.not_mem_nil, fun f hf => ?_⟩,
    fun h => absurd h listNatI_not_univ⟩
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf
  rw [fieldI_ctorI, fieldI_ctorI]
  exact nil_related

/-- **Negative**: a constructor applied to fields that are not related is not related: `[a]` and
`[a, b]` have the tails `[]` and `[b]`, two different constructors, so they are not related as
far as the token saying that the tail is the empty list observes. -/
theorem single_pair_unrelated (a b : Ideal) :
    ¬ RT true (.arg consK 1 [] (.tag nilK)) listNatI (ctorI consK [a, ctorI nilK []])
      (ctorI consK [a, ctorI consK [b, ctorI nilK []]]) := by
  intro h
  have h₁ := ((RT.ctorArg_iff.1 h).1 listNatI_mem).2 .self rfl
  rw [fieldI_ctorI, fieldI_ctorI] at h₁
  exact nil_cons_unrelated b (ctorI nilK []) h₁

/-- **Negative**: closure under entailment needs the field tokens of a constructor. The tag of
`cons` and the token saying that the tail is the empty list entail that token, and `[a]` and
`[a, b]` are related as far as the tag observes, but not as far as the token observes. -/
theorem closed_needs_fields : ¬ ∀ (v : List Tok) (t : Tok) (T x x' : Ideal), ent v t = true →
    (∀ s ∈ v, s = .tag t.kind → RT true s T x x') → RT true t T x x' := by
  intro h
  refine single_pair_unrelated natI natI (h [.tag consK, .arg consK 1 [] (.tag nilK)]
    (.arg consK 1 [] (.tag nilK)) listNatI _ _ (ent_of_mem (List.mem_cons_of_mem _
      List.mem_cons_self)) fun s _ e => ?_)
  subst e
  exact RT.ctorTag_iff.2 ⟨fun _ => ⟨ctorI_mem_tag _ _, ctorI_mem_tag _ _⟩,
    fun h' => absurd h' listNatI_not_univ⟩

end Declared

end RelationControls
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
