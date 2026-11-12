{-# OPTIONS --safe --without-K #-}
module DependentExamples where
open import NikStructuralExport
open import Agda.Builtin.Unit

higherIdentity : ⊤
higherIdentity = nikStructural 64 ((A : Set₁) → A → A)
  (λ (A : Set₁) (x : A) → x)

dependentApplication : ⊤
dependentApplication = nikStructural 128
  ((A : Set) → (B : A → Set) → ((x : A) → B x) → (x : A) → B x)
  (λ (A : Set) (B : A → Set) (f : (x : A) → B x) (x : A) → f x)
