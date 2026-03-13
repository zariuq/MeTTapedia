import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

namespace Mettapedia.Languages.MeTTa.PureKernel.DeclarationPilotScaffold

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

/-- Small declarative spec used by pilot family modules. -/
structure DeclSpec where
  name : DeclName
  type : PureTm 0
  value? : Option (PureTm 0) := none
deriving Repr

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

end Mettapedia.Languages.MeTTa.PureKernel.DeclarationPilotScaffold
