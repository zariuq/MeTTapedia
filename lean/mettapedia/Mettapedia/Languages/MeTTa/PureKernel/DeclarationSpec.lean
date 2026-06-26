import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

namespace Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction

/-- Small declarative spec used by pilot family modules. -/
structure DeclSpec where
  name : DeclName
  type : PureTm 0
  value? : Option (PureTm 0) := none
deriving DecidableEq, Repr

/-- Reusable proof obligations for pilot declaration specs.
Closedness of spec types and values is already enforced by the `PureTm 0` fields. -/
def DeclSpec.toPair (s : DeclSpec) : DeclName × DeclEntry :=
  (s.name, { type := s.type, value? := s.value? })

/-- Build a declaration environment from concise declaration specs. -/
def envOfSpecs (specs : List DeclSpec) : DeclEnv :=
  ofList (specs.map DeclSpec.toPair)

/-- Reusable proof obligations for pilot declaration specs.
Closedness of spec types and values is already enforced by the `PureTm 0` fields. -/
structure DeclSpecObligations (specs : List DeclSpec) : Prop where
  valuesWellTyped :
    ∀ s ∈ specs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      HasTypeDecl (envOfSpecs specs) .nil (liftClosed v0) (liftClosed s.type)
  noSelfDelta :
    ∀ s ∈ specs, ∀ v0 : PureTm 0,
      s.value? = some v0 →
      v0 ≠ (.const s.name)

/-- Ordered declaration-signature discipline above the operational declaration
environment. This is the right place to add stronger signature theory later
without changing the reduction-preservation boundary. -/
structure SignatureWellFormed (specs : List DeclSpec) : Prop where
  noShadowing : (specs.map DeclSpec.name).Nodup
  obligations : DeclSpecObligations specs

theorem SignatureWellFormed.toDeclSpecObligations {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs) :
    DeclSpecObligations specs :=
  hSig.obligations

/-- Closed declaration types and unfolding values should only mention names
already available in the current signature prefix. -/
def UsesOnlyDeclNamesFrom (allowed : List DeclName) : PureTm n → Prop
  | .var _ => True
  | .const c => c ∈ allowed
  | .u0 => True
  | .u1 => True
  | .pi A B => UsesOnlyDeclNamesFrom allowed A ∧ UsesOnlyDeclNamesFrom allowed B
  | .sigma A B => UsesOnlyDeclNamesFrom allowed A ∧ UsesOnlyDeclNamesFrom allowed B
  | .id A a b =>
      UsesOnlyDeclNamesFrom allowed A ∧
        UsesOnlyDeclNamesFrom allowed a ∧
        UsesOnlyDeclNamesFrom allowed b
  | .lam body => UsesOnlyDeclNamesFrom allowed body
  | .app f a => UsesOnlyDeclNamesFrom allowed f ∧ UsesOnlyDeclNamesFrom allowed a
  | .pair a b => UsesOnlyDeclNamesFrom allowed a ∧ UsesOnlyDeclNamesFrom allowed b
  | .fst p => UsesOnlyDeclNamesFrom allowed p
  | .snd p => UsesOnlyDeclNamesFrom allowed p
  | .refl a => UsesOnlyDeclNamesFrom allowed a

theorem usesOnlyDeclNamesFrom_mono
    {allowed allowed' : List DeclName}
    (hmono : ∀ c : DeclName, c ∈ allowed → c ∈ allowed') :
    ∀ {t : PureTm n},
      UsesOnlyDeclNamesFrom allowed t →
      UsesOnlyDeclNamesFrom allowed' t := by
  intro t hUses
  induction t with
  | var i =>
      simpa [UsesOnlyDeclNamesFrom]
  | const c =>
      exact hmono c hUses
  | u0 =>
      simpa [UsesOnlyDeclNamesFrom]
  | u1 =>
      simpa [UsesOnlyDeclNamesFrom]
  | pi A B ihA ihB =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ihA hUses.1, ihB hUses.2⟩
  | sigma A B ihA ihB =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ihA hUses.1, ihB hUses.2⟩
  | id A a b ihA iha ihb =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ihA hUses.1, iha hUses.2.1, ihb hUses.2.2⟩
  | lam body ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses
  | app f a ihf iha =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ihf hUses.1, iha hUses.2⟩
  | pair a b iha ihb =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨iha hUses.1, ihb hUses.2⟩
  | fst p ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses
  | snd p ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses
  | refl a iha =>
      simpa [UsesOnlyDeclNamesFrom] using iha hUses

theorem usesOnlyDeclNamesFrom_rename
    {allowed : List DeclName} {t : PureTm n} (ρ : Ren n m)
    (hUses : UsesOnlyDeclNamesFrom allowed t) :
    UsesOnlyDeclNamesFrom allowed (rename ρ t) := by
  induction t generalizing m with
  | var i =>
      simpa [UsesOnlyDeclNamesFrom, rename]
  | const c =>
      simpa [UsesOnlyDeclNamesFrom, rename] using hUses
  | u0 =>
      simpa [UsesOnlyDeclNamesFrom, rename]
  | u1 =>
      simpa [UsesOnlyDeclNamesFrom, rename]
  | pi A B ihA ihB =>
      simpa [UsesOnlyDeclNamesFrom, rename] using
        ⟨ihA (ρ := ρ) hUses.1, ihB (ρ := liftRen ρ) hUses.2⟩
  | sigma A B ihA ihB =>
      simpa [UsesOnlyDeclNamesFrom, rename] using
        ⟨ihA (ρ := ρ) hUses.1, ihB (ρ := liftRen ρ) hUses.2⟩
  | id A a b ihA iha ihb =>
      simpa [UsesOnlyDeclNamesFrom, rename] using
        ⟨ihA (ρ := ρ) hUses.1, iha (ρ := ρ) hUses.2.1, ihb (ρ := ρ) hUses.2.2⟩
  | lam body ih =>
      simpa [UsesOnlyDeclNamesFrom, rename] using ih (ρ := liftRen ρ) hUses
  | app f a ihf iha =>
      simpa [UsesOnlyDeclNamesFrom, rename] using
        ⟨ihf (ρ := ρ) hUses.1, iha (ρ := ρ) hUses.2⟩
  | pair a b iha ihb =>
      simpa [UsesOnlyDeclNamesFrom, rename] using
        ⟨iha (ρ := ρ) hUses.1, ihb (ρ := ρ) hUses.2⟩
  | fst p ih =>
      simpa [UsesOnlyDeclNamesFrom, rename] using ih (ρ := ρ) hUses
  | snd p ih =>
      simpa [UsesOnlyDeclNamesFrom, rename] using ih (ρ := ρ) hUses
  | refl a iha =>
      simpa [UsesOnlyDeclNamesFrom, rename] using iha (ρ := ρ) hUses

theorem usesOnlyDeclNamesFrom_subst
    {allowed : List DeclName} :
    ∀ {n m : Nat} {σ : Sub n m} {t : PureTm n},
      (∀ i : Fin n, UsesOnlyDeclNamesFrom allowed (σ i)) →
      UsesOnlyDeclNamesFrom allowed t →
      UsesOnlyDeclNamesFrom allowed (subst σ t) := by
  intro n m σ t hσ hUses
  induction t generalizing m with
  | var i =>
      simpa [subst] using hσ i
  | const c =>
      simpa [UsesOnlyDeclNamesFrom, subst] using hUses
  | u0 =>
      simpa [UsesOnlyDeclNamesFrom, subst]
  | u1 =>
      simpa [UsesOnlyDeclNamesFrom, subst]
  | pi A B ihA ihB =>
      have hσlift : ∀ i : Fin (_ + 1), UsesOnlyDeclNamesFrom allowed (liftSub σ i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [liftSub, UsesOnlyDeclNamesFrom]
        · intro j
          simpa [liftSub] using usesOnlyDeclNamesFrom_rename (ρ := wk) (hUses := hσ j)
      simpa [UsesOnlyDeclNamesFrom, subst] using
        ⟨ihA hσ hUses.1, ihB hσlift hUses.2⟩
  | sigma A B ihA ihB =>
      have hσlift : ∀ i : Fin (_ + 1), UsesOnlyDeclNamesFrom allowed (liftSub σ i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [liftSub, UsesOnlyDeclNamesFrom]
        · intro j
          simpa [liftSub] using usesOnlyDeclNamesFrom_rename (ρ := wk) (hUses := hσ j)
      simpa [UsesOnlyDeclNamesFrom, subst] using
        ⟨ihA hσ hUses.1, ihB hσlift hUses.2⟩
  | id A a b ihA iha ihb =>
      simpa [UsesOnlyDeclNamesFrom, subst] using
        ⟨ihA hσ hUses.1, iha hσ hUses.2.1, ihb hσ hUses.2.2⟩
  | lam body ih =>
      have hσlift : ∀ i : Fin (_ + 1), UsesOnlyDeclNamesFrom allowed (liftSub σ i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [liftSub, UsesOnlyDeclNamesFrom]
        · intro j
          simpa [liftSub] using usesOnlyDeclNamesFrom_rename (ρ := wk) (hUses := hσ j)
      simpa [UsesOnlyDeclNamesFrom, subst] using ih hσlift hUses
  | app f a ihf iha =>
      simpa [UsesOnlyDeclNamesFrom, subst] using ⟨ihf hσ hUses.1, iha hσ hUses.2⟩
  | pair a b iha ihb =>
      simpa [UsesOnlyDeclNamesFrom, subst] using ⟨iha hσ hUses.1, ihb hσ hUses.2⟩
  | fst p ih =>
      simpa [UsesOnlyDeclNamesFrom, subst] using ih hσ hUses
  | snd p ih =>
      simpa [UsesOnlyDeclNamesFrom, subst] using ih hσ hUses
  | refl a iha =>
      simpa [UsesOnlyDeclNamesFrom, subst] using iha hσ hUses

theorem usesOnlyDeclNamesFrom_inst0
    {allowed : List DeclName} {a : PureTm n} {b : PureTm (n + 1)}
    (ha : UsesOnlyDeclNamesFrom allowed a)
    (hb : UsesOnlyDeclNamesFrom allowed b) :
    UsesOnlyDeclNamesFrom allowed (inst0 a b) := by
  have hσ : ∀ i : Fin (n + 1), UsesOnlyDeclNamesFrom allowed (subst0 a i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [subst0] using ha
    · intro j
      simpa [subst0, UsesOnlyDeclNamesFrom]
  simpa [inst0] using usesOnlyDeclNamesFrom_subst hσ hb

def prefixNames (pre : List DeclSpec) : List DeclName :=
  pre.map DeclSpec.name

/-- Prefix-aware admissibility for one declaration spec.
This is the first semantic use of signature order: any unfolding value must
already typecheck against the earlier signature prefix. -/
structure PrefixDeclSpecAdmissible (pre : List DeclSpec) (s : DeclSpec) : Prop where
  fresh : s.name ∉ pre.map DeclSpec.name
  typeUsesEarlier :
    UsesOnlyDeclNamesFrom (prefixNames pre) s.type
  valueUsesEarlier :
    ∀ {v0 : PureTm 0},
      s.value? = some v0 →
      UsesOnlyDeclNamesFrom (prefixNames pre) v0
  valueWellTyped :
    ∀ {v0 : PureTm 0},
      s.value? = some v0 →
      HasTypeDecl (envOfSpecs pre) .nil (liftClosed v0) (liftClosed s.type)
  noSelfDelta :
    ∀ {v0 : PureTm 0},
      s.value? = some v0 →
      v0 ≠ (.const s.name)

/-- Ordered signature checking, left to right, against earlier declarations only. -/
def PrefixSignatureWellFormed : List DeclSpec → List DeclSpec → Prop
  | _, [] => True
  | pre, s :: rest =>
      PrefixDeclSpecAdmissible pre s ∧
        PrefixSignatureWellFormed (pre ++ [s]) rest

abbrev SignatureWellFormedPrefix (specs : List DeclSpec) : Prop :=
  PrefixSignatureWellFormed [] specs

theorem PrefixSignatureWellFormed.take
    {acc pre post : List DeclSpec}
    (hSig : PrefixSignatureWellFormed acc (pre ++ post)) :
    PrefixSignatureWellFormed acc pre := by
  induction pre generalizing acc post with
  | nil =>
      simp [PrefixSignatureWellFormed]
  | cons s rest ih =>
      simp [List.cons_append, PrefixSignatureWellFormed] at hSig ⊢
      rcases hSig with ⟨hs, hrest⟩
      exact ⟨hs, ih hrest⟩

theorem SignatureWellFormedPrefix.take
    {pre post : List DeclSpec}
    (hSig : SignatureWellFormedPrefix (pre ++ post)) :
    SignatureWellFormedPrefix pre := by
  simpa [SignatureWellFormedPrefix] using
    (PrefixSignatureWellFormed.take (acc := []) (pre := pre) (post := post) hSig)

theorem red_preserves_usesOnlyDeclNamesFrom
    {allowed : List DeclName} {t u : PureTm n}
    (hRed : Red t u) :
    UsesOnlyDeclNamesFrom allowed t →
    UsesOnlyDeclNamesFrom allowed u := by
  intro hUses
  induction hRed generalizing allowed with
  | betaPi body a =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      exact usesOnlyDeclNamesFrom_inst0 hUses.2 (by simpa [UsesOnlyDeclNamesFrom] using hUses.1)
  | betaSigmaFst a b =>
      simpa [UsesOnlyDeclNamesFrom] using hUses.1
  | betaSigmaSnd a b =>
      simpa [UsesOnlyDeclNamesFrom] using hUses.2
  | congPiDom h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ih hUses.1, hUses.2⟩
  | congPiCod h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, ih hUses.2⟩
  | congSigmaDom h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ih hUses.1, hUses.2⟩
  | congSigmaCod h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, ih hUses.2⟩
  | congIdTy h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ih hUses.1, hUses.2.1, hUses.2.2⟩
  | congIdLeft h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, ih hUses.2.1, hUses.2.2⟩
  | congIdRight h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hUses.2.1, ih hUses.2.2⟩
  | congLam h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses
  | congAppFun h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ih hUses.1, hUses.2⟩
  | congAppArg h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, ih hUses.2⟩
  | congPairFst h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨ih hUses.1, hUses.2⟩
  | congPairSnd h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, ih hUses.2⟩
  | congFst h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses
  | congSnd h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses
  | congRefl h ih =>
      simpa [UsesOnlyDeclNamesFrom] using ih hUses

theorem prefixSignatureWellFormed_nodup
    {pre specs : List DeclSpec}
    (hPre : (prefixNames pre).Nodup)
    (hSig : PrefixSignatureWellFormed pre specs) :
    (prefixNames (pre ++ specs)).Nodup := by
  induction specs generalizing pre with
  | nil =>
      simpa [PrefixSignatureWellFormed] using hPre
  | cons s rest ih =>
      rcases hSig with ⟨hs, hrest⟩
      have hPreSnoc : (prefixNames (pre ++ [s])).Nodup := by
        have hAppend : (prefixNames pre ++ [s.name]).Nodup := by
          exact List.nodup_append.mpr ⟨hPre, by simp, by simpa [prefixNames] using hs.fresh⟩
        simpa [prefixNames] using hAppend
      simpa [prefixNames, List.append_assoc] using ih hPreSnoc hrest

theorem SignatureWellFormedPrefix.noShadowing
    {specs : List DeclSpec}
    (hSig : SignatureWellFormedPrefix specs) :
    (prefixNames specs).Nodup := by
  simpa [SignatureWellFormedPrefix] using
    prefixSignatureWellFormed_nodup (pre := []) (specs := specs) (by simp [prefixNames]) hSig

theorem SignatureWellFormed.ofPrefix
    {specs : List DeclSpec}
    (hPrefix : SignatureWellFormedPrefix specs)
    (hObligations : DeclSpecObligations specs) :
    SignatureWellFormed specs where
  noShadowing := hPrefix.noShadowing
  obligations := hObligations

theorem PrefixSignatureWellFormed.mem_prefixDeclSpecAdmissible
    {pre specs : List DeclSpec}
    (hPrefix : PrefixSignatureWellFormed pre specs)
    {s : DeclSpec}
    (hs : s ∈ specs) :
    ∃ pre' post,
      specs = pre' ++ s :: post ∧
      PrefixDeclSpecAdmissible (pre ++ pre') s := by
  induction specs generalizing pre with
  | nil =>
      cases hs
  | cons head tail ih =>
      rcases hPrefix with ⟨hHead, hTail⟩
      simp at hs
      rcases hs with rfl | hsTail
      · exact ⟨[], tail, rfl, by simpa using hHead⟩
      · rcases ih hTail hsTail with ⟨pre', post, hEq, hAdm⟩
        exact ⟨head :: pre', post, by simp [hEq], by simpa [List.append_assoc] using hAdm⟩

theorem SignatureWellFormedPrefix.mem_prefixDeclSpecAdmissible
    {specs : List DeclSpec}
    (hPrefix : SignatureWellFormedPrefix specs)
    {s : DeclSpec}
    (hs : s ∈ specs) :
    ∃ pre post,
      specs = pre ++ s :: post ∧
      PrefixDeclSpecAdmissible pre s := by
  simpa [SignatureWellFormedPrefix] using
    PrefixSignatureWellFormed.mem_prefixDeclSpecAdmissible (pre := []) hPrefix hs

theorem entries_envOfSpecs_eq_of_mem_of_nodup
    {specs : List DeclSpec} {s : DeclSpec}
    (hNodup : (specs.map DeclSpec.name).Nodup)
    (hs : s ∈ specs) :
    (envOfSpecs specs).entries s.name = some { type := s.type, value? := s.value? } := by
  induction specs generalizing s with
  | nil =>
      cases hs
  | cons head tail ih =>
      rcases List.nodup_cons.mp hNodup with ⟨hHeadFresh, hTailNodup⟩
      simp at hs
      rcases hs with rfl | hsTail
      · simp [envOfSpecs, DeclarationEnv.ofList, DeclarationEnv.insert, DeclSpec.toPair]
      · have hMemName : s.name ∈ tail.map DeclSpec.name := by
          exact List.mem_map.mpr ⟨s, hsTail, rfl⟩
        have hNameNe : s.name ≠ head.name := by
          intro hEq
          apply hHeadFresh
          simpa [hEq] using hMemName
        have hTail := ih hTailNodup hsTail
        simpa [envOfSpecs, DeclarationEnv.ofList, DeclarationEnv.insert, DeclSpec.toPair, hNameNe]
          using hTail

theorem typeOf_envOfSpecs_eq_of_mem_of_nodup
    {specs : List DeclSpec} {s : DeclSpec}
    (hNodup : (specs.map DeclSpec.name).Nodup)
    (hs : s ∈ specs) :
    typeOf? (envOfSpecs specs) s.name = some s.type := by
  unfold DeclarationEnv.typeOf?
  simp [entries_envOfSpecs_eq_of_mem_of_nodup hNodup hs]

theorem valueOf_envOfSpecs_eq_of_mem_some_of_nodup
    {specs : List DeclSpec} {s : DeclSpec} {v0 : PureTm 0}
    (hNodup : (specs.map DeclSpec.name).Nodup)
    (hs : s ∈ specs)
    (hVal : s.value? = some v0) :
    valueOf? (envOfSpecs specs) s.name = some v0 := by
  unfold DeclarationEnv.valueOf?
  simp [hVal, entries_envOfSpecs_eq_of_mem_of_nodup hNodup hs]

theorem valueOf_envOfSpecs_eq_none_of_mem_none_of_nodup
    {specs : List DeclSpec} {s : DeclSpec}
    (hNodup : (specs.map DeclSpec.name).Nodup)
    (hs : s ∈ specs)
    (hVal : s.value? = none) :
    valueOf? (envOfSpecs specs) s.name = none := by
  unfold DeclarationEnv.valueOf?
  simp [hVal, entries_envOfSpecs_eq_of_mem_of_nodup hNodup hs]

theorem SignatureWellFormed.entries_eq_of_mem
    {specs : List DeclSpec} (hSig : SignatureWellFormed specs) {s : DeclSpec}
    (hs : s ∈ specs) :
    (envOfSpecs specs).entries s.name = some { type := s.type, value? := s.value? } :=
  entries_envOfSpecs_eq_of_mem_of_nodup hSig.noShadowing hs

theorem SignatureWellFormed.typeOf_eq_of_mem
    {specs : List DeclSpec} (hSig : SignatureWellFormed specs) {s : DeclSpec}
    (hs : s ∈ specs) :
    typeOf? (envOfSpecs specs) s.name = some s.type :=
  typeOf_envOfSpecs_eq_of_mem_of_nodup hSig.noShadowing hs

theorem SignatureWellFormed.valueOf_eq_of_mem_some
    {specs : List DeclSpec} (hSig : SignatureWellFormed specs) {s : DeclSpec} {v0 : PureTm 0}
    (hs : s ∈ specs) (hVal : s.value? = some v0) :
    valueOf? (envOfSpecs specs) s.name = some v0 :=
  valueOf_envOfSpecs_eq_of_mem_some_of_nodup hSig.noShadowing hs hVal

theorem SignatureWellFormed.valueOf_eq_of_mem_none
    {specs : List DeclSpec} (hSig : SignatureWellFormed specs) {s : DeclSpec}
    (hs : s ∈ specs) (hVal : s.value? = none) :
    valueOf? (envOfSpecs specs) s.name = none :=
  valueOf_envOfSpecs_eq_none_of_mem_none_of_nodup hSig.noShadowing hs hVal

/-- Generic typing helper for declared constants. -/
theorem hasType_const_from_lookup {E : DeclEnv} {Γ : Ctx n} {c : DeclName} {A0 : PureTm 0}
    (h : typeOf? E c = some A0) :
    HasTypeDecl E Γ (.const c) (liftClosed A0) :=
  .const h

/-- Generic unfolding helper for declared constants at depth `0`. -/
theorem red_const_from_unfold0 {E : DeclEnv} {c : DeclName} {v : PureTm 0}
    (h : valueOf? E c = some v) :
    RedDecl E ((.const c : PureTm 0)) (liftClosed v) := by
  exact .deltaConst h

/-- If all declaration specs are non-unfolding (`value? = none`), the
generated declaration environment is fail-closed for `valueOf?`. -/
theorem entries_envOfSpecs_some_implies_valueNone
    (specs : List DeclSpec)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    ∀ {c : DeclName} {a : DeclEntry}, (envOfSpecs specs).entries c = some a → a.value? = none := by
  induction specs with
  | nil =>
      intro c a h
      simp [envOfSpecs, DeclarationEnv.ofList, DeclarationEnv.empty] at h
  | cons s rest ih =>
      intro c a h
      have hs : s.value? = none := hNone s (by simp)
      have hRest : ∀ r ∈ rest, r.value? = none := by
        intro r hr
        exact hNone r (by simp [hr])
      unfold envOfSpecs at h
      simp [DeclarationEnv.ofList] at h
      unfold DeclarationEnv.insert at h
      by_cases hEq : c = s.name
      · simp [hEq, DeclSpec.toPair] at h
        cases h
        simp [hs]
      · simp [hEq, DeclSpec.toPair] at h
        exact ih hRest h

/-- Any successful lookup in `envOfSpecs` comes from some source spec with
matching name/type/value fields. -/
theorem entries_envOfSpecs_some_implies_from_specs
    (specs : List DeclSpec) :
    ∀ {c : DeclName} {a : DeclEntry},
      (envOfSpecs specs).entries c = some a →
      ∃ s ∈ specs, s.name = c ∧ s.type = a.type ∧ s.value? = a.value? := by
  induction specs with
  | nil =>
      intro c a h
      simp [envOfSpecs, DeclarationEnv.ofList, DeclarationEnv.empty] at h
  | cons s rest ih =>
      intro c a h
      unfold envOfSpecs at h
      simp [DeclarationEnv.ofList] at h
      unfold DeclarationEnv.insert at h
      by_cases hEq : c = s.name
      · simp [hEq, DeclSpec.toPair] at h
        cases h
        refine ⟨s, by simp, ?_⟩
        simp [hEq]
      · simp [hEq, DeclSpec.toPair] at h
        rcases ih h with ⟨s', hs', hsName, hsType, hsValue⟩
        exact ⟨s', by simp [hs'], hsName, hsType, hsValue⟩

theorem SignatureWellFormedPrefix.lookup_type_uses_earlier
    {specs : List DeclSpec}
    (hPrefix : SignatureWellFormedPrefix specs)
    {c : DeclName} {A0 : PureTm 0}
    (hType : typeOf? (envOfSpecs specs) c = some A0) :
    ∃ s pre post,
      specs = pre ++ s :: post ∧
      s.name = c ∧
      s.type = A0 ∧
      UsesOnlyDeclNamesFrom (prefixNames pre) A0 ∧
      c ∉ prefixNames pre := by
  unfold DeclarationEnv.typeOf? at hType
  cases hEntries : (envOfSpecs specs).entries c with
  | none =>
      simp [hEntries] at hType
  | some a =>
      have hA : a.type = A0 := by
        simpa [hEntries] using hType
      rcases entries_envOfSpecs_some_implies_from_specs specs hEntries with
        ⟨s, hsMem, hsName, hsType, _hsValue⟩
      rcases hPrefix.mem_prefixDeclSpecAdmissible hsMem with ⟨pre, post, hSplit, hAdm⟩
      have hTypeEarlier : UsesOnlyDeclNamesFrom (prefixNames pre) A0 := by
        simpa [hsType, hA] using hAdm.typeUsesEarlier
      exact ⟨s, pre, post, hSplit, hsName, by simpa [hA] using hsType, hTypeEarlier,
        by simpa [prefixNames, hsName] using hAdm.fresh⟩

theorem SignatureWellFormedPrefix.lookup_value_uses_earlier
    {specs : List DeclSpec}
    (hPrefix : SignatureWellFormedPrefix specs)
    {c : DeclName} {v0 : PureTm 0}
    (hVal : valueOf? (envOfSpecs specs) c = some v0) :
    ∃ s pre post,
      specs = pre ++ s :: post ∧
      s.name = c ∧
      s.value? = some v0 ∧
      UsesOnlyDeclNamesFrom (prefixNames pre) v0 ∧
      c ∉ prefixNames pre := by
  unfold DeclarationEnv.valueOf? at hVal
  cases hEntries : (envOfSpecs specs).entries c with
  | none =>
      simp [hEntries] at hVal
  | some a =>
      have hValue : a.value? = some v0 := by
        simpa [hEntries] using hVal
      rcases entries_envOfSpecs_some_implies_from_specs specs hEntries with
        ⟨s, hsMem, hsName, _hsType, hsValue⟩
      have hsValSome : s.value? = some v0 := by
        calc
          s.value? = a.value? := hsValue
          _ = some v0 := hValue
      rcases hPrefix.mem_prefixDeclSpecAdmissible hsMem with ⟨pre, post, hSplit, hAdm⟩
      exact ⟨s, pre, post, hSplit, hsName, hsValSome, hAdm.valueUsesEarlier hsValSome,
        by simpa [prefixNames, hsName] using hAdm.fresh⟩

theorem envOfSpecs_extends_of_prefix_append
    {pre post : List DeclSpec}
    (hNodup : (prefixNames (pre ++ post)).Nodup) :
    Extends (envOfSpecs pre) (envOfSpecs (pre ++ post)) := by
  intro c entry hEntry
  rcases entries_envOfSpecs_some_implies_from_specs pre hEntry with
    ⟨s, hsMem, hsName, hsType, hsValue⟩
  have hFull :
      (envOfSpecs (pre ++ post)).entries s.name =
        some { type := s.type, value? := s.value? } :=
    entries_envOfSpecs_eq_of_mem_of_nodup hNodup (by simp [hsMem])
  have hEntryEq : entry = { type := s.type, value? := s.value? } := by
    cases entry
    simp at hsType hsValue
    cases hsType
    cases hsValue
    rfl
  simpa [hsName, hEntryEq] using hFull

theorem entries_envOfSpecs_prefix_eq_of_mem
    {pre post : List DeclSpec}
    (hNodup : (prefixNames (pre ++ post)).Nodup)
    {c : DeclName}
    (hc : c ∈ prefixNames pre) :
    (envOfSpecs (pre ++ post)).entries c = (envOfSpecs pre).entries c := by
  rcases List.mem_map.mp hc with ⟨s, hsMem, hsName⟩
  have hPreNodup : (prefixNames pre).Nodup := by
    have hAppend : (prefixNames pre ++ prefixNames post).Nodup := by
      simpa [prefixNames] using hNodup
    exact (List.nodup_append.mp hAppend).1
  have hFull :
      (envOfSpecs (pre ++ post)).entries s.name =
        some { type := s.type, value? := s.value? } :=
    entries_envOfSpecs_eq_of_mem_of_nodup hNodup (by simp [hsMem])
  have hPre :
      (envOfSpecs pre).entries s.name =
        some { type := s.type, value? := s.value? } :=
    entries_envOfSpecs_eq_of_mem_of_nodup hPreNodup hsMem
  simpa [hsName] using hFull.trans hPre.symm

theorem typeOf_envOfSpecs_prefix_eq_of_mem
    {pre post : List DeclSpec}
    (hNodup : (prefixNames (pre ++ post)).Nodup)
    {c : DeclName}
    (hc : c ∈ prefixNames pre) :
    typeOf? (envOfSpecs (pre ++ post)) c = typeOf? (envOfSpecs pre) c := by
  unfold DeclarationEnv.typeOf?
  simp [entries_envOfSpecs_prefix_eq_of_mem hNodup hc]

theorem valueOf_envOfSpecs_prefix_eq_of_mem
    {pre post : List DeclSpec}
    (hNodup : (prefixNames (pre ++ post)).Nodup)
    {c : DeclName}
    (hc : c ∈ prefixNames pre) :
    valueOf? (envOfSpecs (pre ++ post)) c = valueOf? (envOfSpecs pre) c := by
  unfold DeclarationEnv.valueOf?
  simp [entries_envOfSpecs_prefix_eq_of_mem hNodup hc]

theorem SignatureWellFormedPrefix.lookup_value_from_earlier_prefix
    {specs : List DeclSpec}
    (hPrefix : SignatureWellFormedPrefix specs)
    {c : DeclName} {v0 : PureTm 0}
    (hVal : valueOf? (envOfSpecs specs) c = some v0) :
    ∃ s pre post,
      specs = pre ++ s :: post ∧
      s.name = c ∧
      s.value? = some v0 ∧
      HasTypeDecl (envOfSpecs pre) .nil (liftClosed v0) (liftClosed s.type) ∧
      UsesOnlyDeclNamesFrom (prefixNames pre) v0 ∧
      Extends (envOfSpecs pre) (envOfSpecs specs) := by
  unfold DeclarationEnv.valueOf? at hVal
  cases hEntries : (envOfSpecs specs).entries c with
  | none =>
      simp [hEntries] at hVal
  | some a =>
      have hValue : a.value? = some v0 := by
        simpa [hEntries] using hVal
      rcases entries_envOfSpecs_some_implies_from_specs specs hEntries with
        ⟨s, hsMem, hsName, _hsType, hsValue⟩
      have hsValSome : s.value? = some v0 := by
        calc
          s.value? = a.value? := hsValue
          _ = some v0 := hValue
      rcases hPrefix.mem_prefixDeclSpecAdmissible hsMem with ⟨pre, post, hSplit, hAdm⟩
      have hExt : Extends (envOfSpecs pre) (envOfSpecs specs) := by
        subst hSplit
        exact envOfSpecs_extends_of_prefix_append hPrefix.noShadowing
      exact ⟨s, pre, post, hSplit, hsName, hsValSome, hAdm.valueWellTyped hsValSome,
        hAdm.valueUsesEarlier hsValSome, hExt⟩

theorem redDecl_prefix_restrict
    {pre post : List DeclSpec}
    (hSig : SignatureWellFormedPrefix (pre ++ post))
    {t u : PureTm n}
    (hRed : RedDecl (envOfSpecs (pre ++ post)) t u) :
    UsesOnlyDeclNamesFrom (prefixNames pre) t →
    RedDecl (envOfSpecs pre) t u ∧ UsesOnlyDeclNamesFrom (prefixNames pre) u := by
  intro hUses
  induction hRed with
  | core hred =>
      exact ⟨.core hred, red_preserves_usesOnlyDeclNamesFrom hred hUses⟩
  | @deltaConst k c v hVal =>
      have hc : c ∈ prefixNames pre := by
        simpa [UsesOnlyDeclNamesFrom] using hUses
      have hValPre : valueOf? (envOfSpecs pre) c = some v := by
        simpa [valueOf_envOfSpecs_prefix_eq_of_mem hSig.noShadowing hc] using hVal
      have hPreSig : SignatureWellFormedPrefix pre :=
        SignatureWellFormedPrefix.take (pre := pre) (post := post) hSig
      rcases hPreSig.lookup_value_uses_earlier hValPre with
        ⟨s, pre', post', hSplit, hsName, hsValSome, hEarlier, _⟩
      have hSub : ∀ d : DeclName, d ∈ prefixNames pre' → d ∈ prefixNames pre := by
        intro d hd
        subst hSplit
        simpa [prefixNames, List.mem_append] using (Or.inl hd)
      have hv : UsesOnlyDeclNamesFrom (prefixNames pre) v :=
        usesOnlyDeclNamesFrom_mono hSub hEarlier
      have hLift : UsesOnlyDeclNamesFrom (prefixNames pre) (liftClosed (n := k) v) := by
        change UsesOnlyDeclNamesFrom (prefixNames pre) (rename (fun i : Fin 0 => nomatch i) v)
        exact usesOnlyDeclNamesFrom_rename (ρ := fun i : Fin 0 => nomatch i) (t := v) hv
      exact ⟨.deltaConst hValPre, hLift⟩
  | congPiDom hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.1 with ⟨hPre, hPreUses⟩
      exact ⟨.congPiDom hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hPreUses, hUses.2⟩⟩
  | congPiCod hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.2 with ⟨hPre, hPreUses⟩
      exact ⟨.congPiCod hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hPreUses⟩⟩
  | congSigmaDom hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.1 with ⟨hPre, hPreUses⟩
      exact ⟨.congSigmaDom hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hPreUses, hUses.2⟩⟩
  | congSigmaCod hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.2 with ⟨hPre, hPreUses⟩
      exact ⟨.congSigmaCod hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hPreUses⟩⟩
  | congIdTy hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.1 with ⟨hPre, hPreUses⟩
      exact ⟨.congIdTy hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hPreUses, hUses.2.1, hUses.2.2⟩⟩
  | congIdLeft hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.2.1 with ⟨hPre, hPreUses⟩
      exact ⟨.congIdLeft hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hPreUses, hUses.2.2⟩⟩
  | congIdRight hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.2.2 with ⟨hPre, hPreUses⟩
      exact ⟨.congIdRight hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hUses.2.1, hPreUses⟩⟩
  | congLam hstep ih =>
      rcases ih hUses with ⟨hPre, hPreUses⟩
      exact ⟨.congLam hPre, by simpa [UsesOnlyDeclNamesFrom] using hPreUses⟩
  | congAppFun hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.1 with ⟨hPre, hPreUses⟩
      exact ⟨.congAppFun hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hPreUses, hUses.2⟩⟩
  | congAppArg hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.2 with ⟨hPre, hPreUses⟩
      exact ⟨.congAppArg hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hPreUses⟩⟩
  | congPairFst hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.1 with ⟨hPre, hPreUses⟩
      exact ⟨.congPairFst hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hPreUses, hUses.2⟩⟩
  | congPairSnd hstep ih =>
      simp [UsesOnlyDeclNamesFrom] at hUses
      rcases ih hUses.2 with ⟨hPre, hPreUses⟩
      exact ⟨.congPairSnd hPre, by simpa [UsesOnlyDeclNamesFrom] using ⟨hUses.1, hPreUses⟩⟩
  | congFst hstep ih =>
      rcases ih hUses with ⟨hPre, hPreUses⟩
      exact ⟨.congFst hPre, by simpa [UsesOnlyDeclNamesFrom] using hPreUses⟩
  | congSnd hstep ih =>
      rcases ih hUses with ⟨hPre, hPreUses⟩
      exact ⟨.congSnd hPre, by simpa [UsesOnlyDeclNamesFrom] using hPreUses⟩
  | congRefl hstep ih =>
      rcases ih hUses with ⟨hPre, hPreUses⟩
      exact ⟨.congRefl hPre, by simpa [UsesOnlyDeclNamesFrom] using hPreUses⟩

theorem redStarDecl_prefix_restrict
    {pre post : List DeclSpec}
    (hSig : SignatureWellFormedPrefix (pre ++ post))
    {t u : PureTm n}
    (hRed : RedStarDecl (envOfSpecs (pre ++ post)) t u) :
    UsesOnlyDeclNamesFrom (prefixNames pre) t →
    RedStarDecl (envOfSpecs pre) t u ∧ UsesOnlyDeclNamesFrom (prefixNames pre) u := by
  induction hRed with
  | refl =>
      intro hUses
      exact ⟨RedStarDecl.refl _, hUses⟩
  | tail hxy hyz ih =>
      intro hUses
      rcases ih hUses with ⟨hxyPre, hxyUses⟩
      rcases redDecl_prefix_restrict (pre := pre) (post := post) hSig hyz hxyUses with
        ⟨hyzPre, hyzUses⟩
      exact ⟨RedStarDecl.tail hxyPre hyzPre, hyzUses⟩

theorem SignatureWellFormedPrefix.convDecl_prefix_restrict_of_church_rosser
    {pre post : List DeclSpec}
    (hSig : SignatureWellFormedPrefix (pre ++ post))
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs (pre ++ post)))
    {t u : PureTm n}
    (hConv : ConvDecl (envOfSpecs (pre ++ post)) t u)
    (ht : UsesOnlyDeclNamesFrom (prefixNames pre) t)
    (hu : UsesOnlyDeclNamesFrom (prefixNames pre) u) :
    ConvDecl (envOfSpecs pre) t u := by
  rcases hCR hConv with ⟨w, htw, huw⟩
  rcases redStarDecl_prefix_restrict (pre := pre) (post := post) hSig htw ht with
    ⟨htwPre, _hwPre⟩
  rcases redStarDecl_prefix_restrict (pre := pre) (post := post) hSig huw hu with
    ⟨huwPre, _hwPre'⟩
  exact
    Relation.EqvGen.trans _ _ _
      (redStarDecl_implies_conv htwPre)
      (Relation.EqvGen.symm _ _ (redStarDecl_implies_conv huwPre))

/-- Vacuous declaration obligations for non-unfolding signatures. -/
theorem declSpecObligations_of_all_none
    (specs : List DeclSpec)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    DeclSpecObligations specs where
  valuesWellTyped := by
    intro s hs v0 hVal
    have hsNone : s.value? = none := hNone s hs
    simp [hsNone] at hVal
  noSelfDelta := by
    intro s hs v0 hVal
    have hsNone : s.value? = none := hNone s hs
    simp [hsNone] at hVal

theorem valueOf_envOfSpecs_eq_none_of_all_none
    (specs : List DeclSpec)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    ∀ c : DeclName, valueOf? (envOfSpecs specs) c = none := by
  intro c
  have hEntryValueNone :
      ∀ {a : DeclEntry}, (envOfSpecs specs).entries c = some a → a.value? = none :=
    entries_envOfSpecs_some_implies_valueNone specs hNone
  unfold DeclarationEnv.valueOf?
  cases hEntries : (envOfSpecs specs).entries c with
  | none =>
      rfl
  | some a =>
      have ha : a.value? = none := hEntryValueNone hEntries
      simp [ha]

/-- Generic typed-value soundness for declaration environments built from specs:
if every `some` value in the specs is typed at its declared type, then the
resulting environment satisfies `DeclValuesWellTyped`. -/
theorem envOfSpecs_declValuesWellTyped_of_specValues
    (specs : List DeclSpec)
    (hTyped :
      ∀ s ∈ specs, ∀ v0 : PureTm 0,
        s.value? = some v0 →
        HasTypeDecl (envOfSpecs specs) .nil (liftClosed v0) (liftClosed s.type)) :
    DeclValuesWellTyped (envOfSpecs specs) := by
  intro c A0 v0 hType hVal
  unfold DeclarationEnv.typeOf? at hType
  unfold DeclarationEnv.valueOf? at hVal
  cases hEntries : (envOfSpecs specs).entries c with
  | none =>
      simp [hEntries] at hType
  | some a =>
      have hA : a.type = A0 := by
        simpa [hEntries] using hType
      have hv : a.value? = some v0 := by
        simpa [hEntries] using hVal
      rcases entries_envOfSpecs_some_implies_from_specs specs hEntries with
        ⟨s, hsMem, _, hsType, hsValue⟩
      have hsValSome : s.value? = some v0 := by
        calc
          s.value? = a.value? := hsValue
          _ = some v0 := hv
      have hsv : HasTypeDecl (envOfSpecs specs) .nil (liftClosed v0) (liftClosed s.type) :=
        hTyped s hsMem v0 hsValSome
      have hsTypeA0 : s.type = A0 := by
        calc
          s.type = a.type := hsType
          _ = A0 := hA
      simpa [hsTypeA0] using hsv

/-- Generic acyclicity/no-self-unfolding invariant for declaration environments
built from specs: if each unfolding value is not the defining constant itself
at the spec level, the generated env satisfies `noSelfDelta`. -/
theorem envOfSpecs_noSelfDelta_of_specNoSelf
    (specs : List DeclSpec)
    (hNoSelf :
      ∀ s ∈ specs, ∀ v0 : PureTm 0,
        s.value? = some v0 →
        v0 ≠ (.const s.name)) :
    ∀ {c : DeclName} {v0 : PureTm 0},
      valueOf? (envOfSpecs specs) c = some v0 →
      v0 ≠ (.const c) := by
  intro c v0 hVal
  unfold DeclarationEnv.valueOf? at hVal
  cases hEntries : (envOfSpecs specs).entries c with
  | none =>
      simp [hEntries] at hVal
  | some a =>
      have hv : a.value? = some v0 := by
        simpa [hEntries] using hVal
      rcases entries_envOfSpecs_some_implies_from_specs specs hEntries with
        ⟨s, hsMem, hsName, _, hsValue⟩
      have hsValSome : s.value? = some v0 := by
        calc
          s.value? = a.value? := hsValue
          _ = some v0 := hv
      have hNo : v0 ≠ (.const s.name) := hNoSelf s hsMem v0 hsValSome
      intro hEq
      apply hNo
      simpa [hsName] using hEq

/-- Generic well-formedness constructor from per-spec typed-value and
no-self-unfolding obligations. -/
theorem envOfSpecs_wellFormed_of_specObligations
    (specs : List DeclSpec)
    (hObligations : DeclSpecObligations specs) :
    DeclEnvWellFormed (envOfSpecs specs) := by
  refine ⟨?_, ?_⟩
  · exact envOfSpecs_declValuesWellTyped_of_specValues specs hObligations.valuesWellTyped
  · exact envOfSpecs_noSelfDelta_of_specNoSelf specs hObligations.noSelfDelta

theorem SignatureWellFormed.toDeclEnvWellFormed {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs) :
    DeclEnvWellFormed (envOfSpecs specs) :=
  envOfSpecs_wellFormed_of_specObligations specs hSig.obligations

abbrev DeclSpecStarPreservationPackage
    (specs : List DeclSpec) : Prop :=
  ∀ {n : Nat} {Γ : Ctx n} {t u A : PureTm n},
    HasTypeDecl (envOfSpecs specs) Γ t A →
    RedStarDecl (envOfSpecs specs) t u →
    HasTypeDecl (envOfSpecs specs) Γ u A

abbrev DeclSpecStarConfluencePackage
    (specs : List DeclSpec) : Prop :=
  ∀ {n : Nat} {s t₁ t₂ : PureTm n},
    RedStarDecl (envOfSpecs specs) s t₁ →
    RedStarDecl (envOfSpecs specs) s t₂ →
    ∃ u,
      RedStarDecl (envOfSpecs specs) t₁ u ∧
      RedStarDecl (envOfSpecs specs) t₂ u

abbrev DeclSpecPiInjectivityPackage
    (specs : List DeclSpec) : Prop :=
  ∀ {n : Nat} {A A' : PureTm n} {B B' : PureTm (n + 1)},
    ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
      ConvDecl (envOfSpecs specs) A A' ∧
      ConvDecl (envOfSpecs specs) B B'

abbrev DeclSpecSigmaInjectivityPackage
    (specs : List DeclSpec) : Prop :=
  ∀ {n : Nat} {A A' : PureTm n} {B B' : PureTm (n + 1)},
    ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
      ConvDecl (envOfSpecs specs) A A' ∧
      ConvDecl (envOfSpecs specs) B B'

abbrev DeclSpecChurchRosserPackage
    (specs : List DeclSpec) : Prop :=
  DeclEnvWellFormed (envOfSpecs specs) ∧
    DeclSpecStarPreservationPackage specs ∧
    DeclSpecStarConfluencePackage specs ∧
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
      (envOfSpecs specs) ∧
    DeclSpecPiInjectivityPackage specs ∧
    DeclSpecSigmaInjectivityPackage specs

abbrev DeclSpecNoValuesNormalizationPackage
    (specs : List DeclSpec)
    (hNone : ∀ s ∈ specs, s.value? = none) : Prop :=
  (∀ {n : Nat} {A B : PureTm n}
      {w : DeclarationSemantics.DefEqDeclWitness (envOfSpecs specs) A B},
      DeclarationSemantics.defEqByNormalizationDeclOfNoValues?
          (envOfSpecs specs)
          (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
          A B = some w →
        ConvDecl (envOfSpecs specs) A B) ∧
    (∀ {n : Nat} {A B : PureTm n},
      DeclarationSemantics.defEqByNormalizationDeclOfNoValues?
          (envOfSpecs specs)
          (valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
          A B ≠ none →
        ConvDecl (envOfSpecs specs) A B)

abbrev DeclSpecAndNoValuesPackage
    (specs : List DeclSpec)
    (hNone : ∀ s ∈ specs, s.value? = none) : Prop :=
  DeclSpecChurchRosserPackage specs ∧
    DeclSpecNoValuesNormalizationPackage specs hNone

theorem DeclSpecChurchRosserPackage.wellFormed
    {specs : List DeclSpec}
    (hPkg : DeclSpecChurchRosserPackage specs) :
    DeclEnvWellFormed (envOfSpecs specs) :=
  hPkg.1

theorem DeclSpecChurchRosserPackage.starPreservation
    {specs : List DeclSpec}
    (hPkg : DeclSpecChurchRosserPackage specs) :
    DeclSpecStarPreservationPackage specs :=
  hPkg.2.1

theorem DeclSpecChurchRosserPackage.starConfluence
    {specs : List DeclSpec}
    (hPkg : DeclSpecChurchRosserPackage specs) :
    DeclSpecStarConfluencePackage specs :=
  hPkg.2.2.1

theorem DeclSpecChurchRosserPackage.declChurchRosser
    {specs : List DeclSpec}
    (hPkg : DeclSpecChurchRosserPackage specs) :
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
      (envOfSpecs specs) :=
  hPkg.2.2.2.1

theorem DeclSpecChurchRosserPackage.piInjective
    {specs : List DeclSpec}
    (hPkg : DeclSpecChurchRosserPackage specs) :
    DeclSpecPiInjectivityPackage specs :=
  hPkg.2.2.2.2.1

theorem DeclSpecChurchRosserPackage.sigmaInjective
    {specs : List DeclSpec}
    (hPkg : DeclSpecChurchRosserPackage specs) :
    DeclSpecSigmaInjectivityPackage specs :=
  hPkg.2.2.2.2.2

theorem DeclSpecAndNoValuesPackage.asChurchRosser
    {specs : List DeclSpec}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hPkg : DeclSpecAndNoValuesPackage specs hNone) :
    DeclSpecChurchRosserPackage specs :=
  hPkg.1

theorem DeclSpecAndNoValuesPackage.normalization
    {specs : List DeclSpec}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hPkg : DeclSpecAndNoValuesPackage specs hNone) :
    DeclSpecNoValuesNormalizationPackage specs hNone :=
  hPkg.2

/-- One-step subject reduction for environments built from checked declaration
specs. This packages the declaration-level preservation theorem behind the
same spec obligations used by the pilot admission boundary. -/
theorem DeclSpecObligations.redDecl_step_preserves_type_of_injective
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hr : RedDecl (envOfSpecs specs) t t') :
    HasTypeDecl (envOfSpecs specs) Γ t' A := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redDecl_step_preserves_type_of_injective
    (E := envOfSpecs specs)
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
    (ht := ht)
    (hr := hr)

/-- Star-closure subject reduction for environments built from checked
declaration specs. This is the strongest generic interface currently proved:
checked spec obligations imply preservation for every declaration-aware
reduction sequence in the resulting environment. -/
theorem DeclSpecObligations.redStarDecl_preserves_type_of_injective
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_preserves_type_of_injective
    (E := envOfSpecs specs)
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
    (ht := ht)
    (hs := hs)

/-- One-step subject reduction for ordered checked signatures. -/
theorem SignatureWellFormed.redDecl_step_preserves_type_of_injective
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hr : RedDecl (envOfSpecs specs) t t') :
    HasTypeDecl (envOfSpecs specs) Γ t' A :=
  hSig.obligations.redDecl_step_preserves_type_of_injective
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (ht := ht)
    (hr := hr)

/-- Star-closure subject reduction for ordered checked signatures. -/
theorem SignatureWellFormed.redStarDecl_preserves_type_of_injective
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (piInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    (sigmaInjective :
      ∀ {k : Nat} {A A' : PureTm k} {B B' : PureTm (k + 1)},
        ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
          ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B')
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A :=
  hSig.obligations.redStarDecl_preserves_type_of_injective
    (piInjective := piInjective)
    (sigmaInjective := sigmaInjective)
    (ht := ht)
    (hs := hs)

/-- One-step subject reduction for checked non-unfolding signatures. In this
fragment declaration-aware conversion collapses to the core conversion
relation, so Pi/Sigma injectivity needs no extra assumptions. -/
theorem DeclSpecObligations.redDecl_step_preserves_type_of_all_none
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hr : RedDecl (envOfSpecs specs) t t') :
    HasTypeDecl (envOfSpecs specs) Γ t' A := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redDecl_step_preserves_type_of_no_values
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
    (ht := ht)
    (hr := hr)

/-- Star-closure subject reduction for checked non-unfolding signatures. -/
theorem DeclSpecObligations.redStarDecl_preserves_type_of_all_none
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_preserves_type_of_no_values
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
    (ht := ht)
    (hs := hs)

/-- One-step subject reduction for ordered checked non-unfolding signatures. -/
theorem SignatureWellFormed.redDecl_step_preserves_type_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hr : RedDecl (envOfSpecs specs) t t') :
    HasTypeDecl (envOfSpecs specs) Γ t' A :=
  hSig.obligations.redDecl_step_preserves_type_of_all_none
    (hNone := hNone)
    (ht := ht)
    (hr := hr)

/-- Star-closure subject reduction for ordered checked non-unfolding
signatures. -/
theorem SignatureWellFormed.redStarDecl_preserves_type_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A :=
  hSig.obligations.redStarDecl_preserves_type_of_all_none
    (hNone := hNone)
    (ht := ht)
    (hs := hs)

/-- Confluence of declaration-aware multi-step reduction for checked
non-unfolding signatures. -/
theorem DeclSpecObligations.redStarDecl_confluence_of_all_none
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {s t₁ t₂ : PureTm n}
    (h₁ : RedStarDecl (envOfSpecs specs) s t₁)
    (h₂ : RedStarDecl (envOfSpecs specs) s t₂) :
    ∃ u,
      RedStarDecl (envOfSpecs specs) t₁ u ∧
      RedStarDecl (envOfSpecs specs) t₂ u := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_confluence_of_no_values
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    h₁ h₂

/-- Church-Rosser for declaration-aware conversion on checked non-unfolding
signatures. -/
theorem DeclSpecObligations.church_rosser_convDecl_of_all_none
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {s t : PureTm n}
    (h : ConvDecl (envOfSpecs specs) s t) :
    ∃ u,
      RedStarDecl (envOfSpecs specs) s u ∧
      RedStarDecl (envOfSpecs specs) t u := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.church_rosser_convDecl_of_no_values
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    h

/-- Pi injectivity for checked non-unfolding signatures. This is the safe
declaration-side fragment where conversion collapses back to the core calculus,
so Pi-shape recovery needs no extra environment-specific hypotheses. -/
theorem DeclSpecObligations.pi_injectivity_decl_of_all_none
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B')) :
    ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B' := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.pi_injectivity_decl_of_no_values
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    h

/-- Sigma injectivity for checked non-unfolding signatures. -/
theorem DeclSpecObligations.sigma_injectivity_decl_of_all_none
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B')) :
    ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B' := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.sigma_injectivity_decl_of_no_values
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    h

/-- Confluence of declaration-aware multi-step reduction for ordered checked
non-unfolding signatures. -/
theorem SignatureWellFormed.redStarDecl_confluence_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {s t₁ t₂ : PureTm n}
    (h₁ : RedStarDecl (envOfSpecs specs) s t₁)
    (h₂ : RedStarDecl (envOfSpecs specs) s t₂) :
    ∃ u,
      RedStarDecl (envOfSpecs specs) t₁ u ∧
      RedStarDecl (envOfSpecs specs) t₂ u :=
  hSig.obligations.redStarDecl_confluence_of_all_none
    (hNone := hNone)
    h₁ h₂

/-- Church-Rosser for declaration-aware conversion on ordered checked
non-unfolding signatures. -/
theorem SignatureWellFormed.church_rosser_convDecl_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {s t : PureTm n}
    (h : ConvDecl (envOfSpecs specs) s t) :
    ∃ u,
      RedStarDecl (envOfSpecs specs) s u ∧
      RedStarDecl (envOfSpecs specs) t u :=
  hSig.obligations.church_rosser_convDecl_of_all_none
    (hNone := hNone)
    h

theorem SignatureWellFormed.declChurchRosser_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
      (envOfSpecs specs) :=
  hSig.church_rosser_convDecl_of_all_none hNone

/-- Pi injectivity for ordered checked non-unfolding signatures. -/
theorem SignatureWellFormed.pi_injectivity_decl_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B')) :
    ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B' :=
  hSig.obligations.pi_injectivity_decl_of_all_none
    (hNone := hNone)
    h

/-- Sigma injectivity for ordered checked non-unfolding signatures. -/
theorem SignatureWellFormed.sigma_injectivity_decl_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (h : ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B')) :
    ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B' :=
  hSig.obligations.sigma_injectivity_decl_of_all_none
    (hNone := hNone)
    h

/-- Pi injectivity for terms that stay within an earlier non-unfolding prefix,
even when the ambient checked environment is larger and value-bearing. The
value-bearing part is handled honestly through the explicit Church-Rosser
hypothesis on the full environment. -/
theorem SignatureWellFormedPrefix.pi_injectivity_decl_of_prefix_all_none_of_church_rosser
    {pre post : List DeclSpec}
    (hSig : SignatureWellFormedPrefix (pre ++ post))
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs (pre ++ post)))
    (hNone : ∀ s ∈ pre, s.value? = none)
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (hUses : UsesOnlyDeclNamesFrom (prefixNames pre) (.pi A B))
    (hUses' : UsesOnlyDeclNamesFrom (prefixNames pre) (.pi A' B'))
    (h :
      ConvDecl (envOfSpecs (pre ++ post)) (.pi A B) (.pi A' B')) :
    ConvDecl (envOfSpecs (pre ++ post)) A A' ∧
      ConvDecl (envOfSpecs (pre ++ post)) B B' := by
  have hPreConv :
      ConvDecl (envOfSpecs pre) (.pi A B) (.pi A' B') :=
    SignatureWellFormedPrefix.convDecl_prefix_restrict_of_church_rosser
      (pre := pre) (post := post) hSig hCR h hUses hUses'
  have hPrePrefix : SignatureWellFormedPrefix pre :=
    SignatureWellFormedPrefix.take (pre := pre) (post := post) hSig
  have hPreSig : SignatureWellFormed pre :=
    SignatureWellFormed.ofPrefix hPrePrefix
      (declSpecObligations_of_all_none pre hNone)
  have hPreInj :
      ConvDecl (envOfSpecs pre) A A' ∧ ConvDecl (envOfSpecs pre) B B' :=
    hPreSig.pi_injectivity_decl_of_all_none hNone hPreConv
  have hExt :
      Extends (envOfSpecs pre) (envOfSpecs (pre ++ post)) :=
    envOfSpecs_extends_of_prefix_append hSig.noShadowing
  exact
    ⟨ convDecl_monotone hExt hPreInj.1
    , convDecl_monotone hExt hPreInj.2
    ⟩

/-- Sigma injectivity for terms that stay within an earlier non-unfolding
prefix, under the same explicit full-environment Church-Rosser hypothesis. -/
theorem SignatureWellFormedPrefix.sigma_injectivity_decl_of_prefix_all_none_of_church_rosser
    {pre post : List DeclSpec}
    (hSig : SignatureWellFormedPrefix (pre ++ post))
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs (pre ++ post)))
    (hNone : ∀ s ∈ pre, s.value? = none)
    {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (hUses : UsesOnlyDeclNamesFrom (prefixNames pre) (.sigma A B))
    (hUses' : UsesOnlyDeclNamesFrom (prefixNames pre) (.sigma A' B'))
    (h :
      ConvDecl (envOfSpecs (pre ++ post)) (.sigma A B) (.sigma A' B')) :
    ConvDecl (envOfSpecs (pre ++ post)) A A' ∧
      ConvDecl (envOfSpecs (pre ++ post)) B B' := by
  have hPreConv :
      ConvDecl (envOfSpecs pre) (.sigma A B) (.sigma A' B') :=
    SignatureWellFormedPrefix.convDecl_prefix_restrict_of_church_rosser
      (pre := pre) (post := post) hSig hCR h hUses hUses'
  have hPrePrefix : SignatureWellFormedPrefix pre :=
    SignatureWellFormedPrefix.take (pre := pre) (post := post) hSig
  have hPreSig : SignatureWellFormed pre :=
    SignatureWellFormed.ofPrefix hPrePrefix
      (declSpecObligations_of_all_none pre hNone)
  have hPreInj :
      ConvDecl (envOfSpecs pre) A A' ∧ ConvDecl (envOfSpecs pre) B B' :=
    hPreSig.sigma_injectivity_decl_of_all_none hNone hPreConv
  have hExt :
      Extends (envOfSpecs pre) (envOfSpecs (pre ++ post)) :=
    envOfSpecs_extends_of_prefix_append hSig.noShadowing
  exact
    ⟨ convDecl_monotone hExt hPreInj.1
    , convDecl_monotone hExt hPreInj.2
    ⟩

/-- Confluence of declaration-aware multi-step reduction for checked
signatures, assuming declaration-aware Church-Rosser is available. This is
the honest value-bearing frontier: we package the consequence, not the proof
of Church-Rosser itself. -/
theorem DeclSpecObligations.redDecl_step_preserves_type_of_church_rosser
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs))
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hr : RedDecl (envOfSpecs specs) t t') :
    HasTypeDecl (envOfSpecs specs) Γ t' A := by
  exact
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redDecl_step_preserves_type_of_church_rosser
      (E := envOfSpecs specs)
      (hCR := hCR)
      (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
      (ht := ht)
      (hr := hr)

theorem DeclSpecObligations.redStarDecl_preserves_type_of_church_rosser
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs))
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A := by
  exact
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
      (E := envOfSpecs specs)
      (hCR := hCR)
      (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
      (ht := ht)
      (hs := hs)

theorem SignatureWellFormed.redDecl_step_preserves_type_of_church_rosser
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs))
    {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hr : RedDecl (envOfSpecs specs) t t') :
    HasTypeDecl (envOfSpecs specs) Γ t' A :=
  hSig.obligations.redDecl_step_preserves_type_of_church_rosser
    hCR ht hr

theorem SignatureWellFormed.redStarDecl_preserves_type_of_church_rosser
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs))
    {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A :=
  hSig.obligations.redStarDecl_preserves_type_of_church_rosser
    hCR ht hs

theorem DeclSpecObligations.redStarDecl_confluence_of_church_rosser
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs))
    {s t₁ t₂ : PureTm n}
    (h₁ : RedStarDecl (envOfSpecs specs) s t₁)
    (h₂ : RedStarDecl (envOfSpecs specs) s t₂) :
    ∃ u,
      RedStarDecl (envOfSpecs specs) t₁ u ∧
      RedStarDecl (envOfSpecs specs) t₂ u := by
  exact
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_confluence_of_church_rosser
      (E := envOfSpecs specs)
      hCR h₁ h₂

/-- Confluence of declaration-aware multi-step reduction for ordered checked
signatures, assuming declaration-aware Church-Rosser is available. -/
theorem SignatureWellFormed.redStarDecl_confluence_of_church_rosser
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs))
    {s t₁ t₂ : PureTm n}
    (h₁ : RedStarDecl (envOfSpecs specs) s t₁)
    (h₂ : RedStarDecl (envOfSpecs specs) s t₂) :
    ∃ u,
      RedStarDecl (envOfSpecs specs) t₁ u ∧
      RedStarDecl (envOfSpecs specs) t₂ u :=
  hSig.obligations.redStarDecl_confluence_of_church_rosser
    hCR h₁ h₂

/-- Checked-signature consequences of declaration-aware Church-Rosser.
This packages the generic value-bearing frontier currently available for
checked environments: subject reduction, confluence, and Pi/Sigma injectivity. -/
theorem DeclSpecObligations.decl_sound_confluent_and_injectivity_of_church_rosser
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs)) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') := by
  exact Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.decl_sound_confluent_and_injectivity_of_church_rosser
      (E := envOfSpecs specs)
      hCR
      (envOfSpecs_wellFormed_of_specObligations specs hObligations)

/-- Ordered checked-signature consequences of declaration-aware Church-Rosser.
This is the current generic boundary for value-bearing declaration environments,
before the normalization/decision layer is established. -/
theorem SignatureWellFormed.decl_sound_confluent_and_injectivity_of_church_rosser
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs)) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') := by
  exact hSig.obligations.decl_sound_confluent_and_injectivity_of_church_rosser hCR

theorem DeclSpecObligations.declSpecChurchRosserPackage_of_church_rosser
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs)) :
    DeclSpecChurchRosserPackage specs := by
  have hWf : DeclEnvWellFormed (envOfSpecs specs) :=
    envOfSpecs_wellFormed_of_specObligations specs hObligations
  refine ⟨hWf, ?_, ?_, hCR, ?_, ?_⟩
  · intro n Γ t u A hTy hStar
    exact
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_preserves_type_of_church_rosser
        (E := envOfSpecs specs)
        (hCR := hCR)
        hWf hTy hStar
  · intro n s t₁ t₂ h₁ h₂
    exact
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.redStarDecl_confluence_of_church_rosser
        (E := envOfSpecs specs)
        hCR h₁ h₂
  · intro n A A' B B' hConv
    exact
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.pi_injectivity_decl_of_church_rosser
        (E := envOfSpecs specs)
        hCR hConv
  · intro n A A' B B' hConv
    exact
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.sigma_injectivity_decl_of_church_rosser
        (E := envOfSpecs specs)
        hCR hConv

theorem SignatureWellFormed.declSpecChurchRosserPackage_of_church_rosser
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs)) :
    DeclSpecChurchRosserPackage specs := by
  exact hSig.obligations.declSpecChurchRosserPackage_of_church_rosser hCR

theorem DeclSpecObligations.declSpecChurchRosserPackage_of_all_none
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    DeclSpecChurchRosserPackage specs := by
  exact
    hObligations.declSpecChurchRosserPackage_of_church_rosser
      (hCR := hObligations.church_rosser_convDecl_of_all_none hNone)

theorem SignatureWellFormed.declSpecChurchRosserPackage_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    DeclSpecChurchRosserPackage specs := by
  exact hSig.obligations.declSpecChurchRosserPackage_of_all_none hNone

/-- Normalization-based declaration-aware definitional equality witness for
checked non-unfolding signatures. -/
def defEqByNormalizationDeclOfAllNone?
    (specs : List DeclSpec)
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (A B : PureTm n) :
    Option (DefEqDeclWitness (envOfSpecs specs) A B) :=
  Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.defEqByNormalizationDeclOfNoValues?
    (E := envOfSpecs specs)
    (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
    A B

/-- Normalization-based declaration-aware definitional equality witness for
ordered checked non-unfolding signatures. -/
def SignatureWellFormed.defEqByNormalizationDeclOfAllNone?
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (A B : PureTm n) :
    Option (DefEqDeclWitness (envOfSpecs specs) A B) :=
  Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec.defEqByNormalizationDeclOfAllNone?
    specs hSig.obligations hNone A B

theorem DeclSpecObligations.defEqByNormalizationDeclOfAllNone?_sound
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B}
    (h : defEqByNormalizationDeclOfAllNone? specs _hObligations hNone A B = some w) :
    ConvDecl (envOfSpecs specs) A B := by
  simpa [defEqByNormalizationDeclOfAllNone?] using
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.defEqByNormalizationDeclOfNoValues?_sound
      (E := envOfSpecs specs)
      (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      (w := w)
      h

theorem SignatureWellFormed.defEqByNormalizationDeclOfAllNone?_sound
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B}
    (h : hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w) :
    ConvDecl (envOfSpecs specs) A B := by
  exact hSig.obligations.defEqByNormalizationDeclOfAllNone?_sound
    (hNone := hNone)
    h

theorem DeclSpecObligations.defEqByNormalizationDeclOfAllNone?_ne_none_implies_conv
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A B : PureTm n}
    (h : defEqByNormalizationDeclOfAllNone? specs _hObligations hNone A B ≠ none) :
    ConvDecl (envOfSpecs specs) A B := by
  simpa [defEqByNormalizationDeclOfAllNone?] using
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.defEqByNormalizationDeclOfNoValues?_ne_none_implies_conv
      (E := envOfSpecs specs)
      (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
      h

theorem SignatureWellFormed.defEqByNormalizationDeclOfAllNone?_ne_none_implies_conv
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {A B : PureTm n}
    (h : hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none) :
    ConvDecl (envOfSpecs specs) A B := by
  exact hSig.obligations.defEqByNormalizationDeclOfAllNone?_ne_none_implies_conv
    (hNone := hNone)
    h

theorem DeclSpecObligations.defEqByNormalizationDeclOfAllNone_not_complete
    {specs : List DeclSpec}
    (_hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    ∃ (Γ : Ctx 1) (t u A : PureTm 1),
      HasTypeDecl (envOfSpecs specs) Γ t A ∧
      HasTypeDecl (envOfSpecs specs) Γ u A ∧
      ConvDecl (envOfSpecs specs) t u ∧
      defEqByNormalizationDeclOfAllNone? specs _hObligations hNone t u = none := by
  simpa [defEqByNormalizationDeclOfAllNone?] using
    Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.defEqByNormalizationDeclOfNoValues_not_complete
      (E := envOfSpecs specs)
      (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)

theorem SignatureWellFormed.defEqByNormalizationDeclOfAllNone_not_complete
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    ∃ (Γ : Ctx 1) (t u A : PureTm 1),
      HasTypeDecl (envOfSpecs specs) Γ t A ∧
      HasTypeDecl (envOfSpecs specs) Γ u A ∧
      ConvDecl (envOfSpecs specs) t u ∧
      hSig.defEqByNormalizationDeclOfAllNone? hNone t u = none := by
  exact hSig.obligations.defEqByNormalizationDeclOfAllNone_not_complete
    (hNone := hNone)

theorem DeclSpecObligations.decl_sound_confluent_and_conversion_of_all_none
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
      defEqByNormalizationDeclOfAllNone? specs hObligations hNone A B = some w →
      ConvDecl (envOfSpecs specs) A B) ∧
    (∀ {A B : PureTm n},
      defEqByNormalizationDeclOfAllNone? specs hObligations hNone A B ≠ none →
      ConvDecl (envOfSpecs specs) A B) := by
  rcases
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.decl_sound_confluent_and_conversion_of_no_values
        (E := envOfSpecs specs)
        (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
        (hWf := envOfSpecs_wellFormed_of_specObligations specs hObligations)
    with ⟨hPres, hConfl, hCR, hPi, hSigma, _hDefEqSound, _hDefEqNeNone⟩
  refine ⟨hPres, hConfl, hCR, hPi, hSigma, ?_, ?_⟩
  · intro A B w hSome
    exact hObligations.defEqByNormalizationDeclOfAllNone?_sound
      (hNone := hNone)
      hSome
  · intro A B hNeNone
    exact hObligations.defEqByNormalizationDeclOfAllNone?_ne_none_implies_conv
      (hNone := hNone)
      hNeNone

theorem SignatureWellFormed.decl_sound_confluent_and_conversion_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧ ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
      hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
      ConvDecl (envOfSpecs specs) A B) ∧
    (∀ {A B : PureTm n},
      hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
      ConvDecl (envOfSpecs specs) A B) := by
  exact hSig.obligations.decl_sound_confluent_and_conversion_of_all_none
    (hNone := hNone)

theorem DeclSpecObligations.declSpecAndNoValuesPackage_of_all_none
    {specs : List DeclSpec}
    (hObligations : DeclSpecObligations specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    DeclSpecAndNoValuesPackage specs hNone := by
  have hCR :
      Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.DeclChurchRosser
        (envOfSpecs specs) := by
    intro n s t hConv
    exact
      hObligations.church_rosser_convDecl_of_all_none
        (hNone := hNone)
        hConv
  have hChurch : DeclSpecChurchRosserPackage specs :=
    hObligations.declSpecChurchRosserPackage_of_church_rosser hCR
  have hNorm :
      DeclSpecNoValuesNormalizationPackage specs hNone := by
    refine ⟨?_, ?_⟩
    · intro n A B w hSome
      exact
        Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.defEqByNormalizationDeclOfNoValues?_sound
          (E := envOfSpecs specs)
          (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
          (w := w)
          hSome
    · intro n A B hNeNone
      exact
        Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics.defEqByNormalizationDeclOfNoValues?_ne_none_implies_conv
          (E := envOfSpecs specs)
          (hNone := valueOf_envOfSpecs_eq_none_of_all_none specs hNone)
          hNeNone
  exact ⟨hChurch, hNorm⟩

theorem SignatureWellFormed.declSpecAndNoValuesPackage_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    DeclSpecAndNoValuesPackage specs hNone := by
  exact hSig.obligations.declSpecAndNoValuesPackage_of_all_none
    (hNone := hNone)

/-- Generic well-formedness for declaration environments built from
non-unfolding declaration specs. -/
theorem envOfSpecs_wellFormed_of_all_none
    (specs : List DeclSpec)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    DeclEnvWellFormed (envOfSpecs specs) := by
  refine ⟨?_, ?_⟩
  · intro c A0 v0 _ hVal
    have hNoneAt : valueOf? (envOfSpecs specs) c = none :=
      valueOf_envOfSpecs_eq_none_of_all_none specs hNone c
    rw [hNoneAt] at hVal
    cases hVal
  · intro c v0 hVal
    have hNoneAt : valueOf? (envOfSpecs specs) c = none :=
      valueOf_envOfSpecs_eq_none_of_all_none specs hNone c
    rw [hNoneAt] at hVal
    cases hVal

end Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
