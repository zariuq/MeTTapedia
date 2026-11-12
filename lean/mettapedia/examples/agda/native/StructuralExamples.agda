{-# OPTIONS --safe --without-K #-}
module StructuralExamples where
open import NikStructuralExport
open import Agda.Builtin.Unit

universe : ⊤
universe = nikStructural 64 Set₁ Set

identity : ⊤
identity = nikStructural 64 ((A : Set) → A → A) (λ (A : Set) (x : A) → x)

application : ⊤
application = nikStructural 64 ((A : Set) → (A → A) → A → A) (λ (A : Set) (f : A → A) (x : A) → f x)

composition : ⊤
composition = nikStructural 128 ((A : Set) → (A → A) → (A → A) → A → A)
  (λ (A : Set) (f g : A → A) (x : A) → f (g x))

constant : ⊤
constant = nikStructural 64 ((A : Set) → Set₁) (λ (A : Set) → Set)
