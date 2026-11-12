{-# OPTIONS --safe --without-K #-}
module HiddenPi where
open import NikStructuralExport
open import Agda.Builtin.Unit
check : ⊤
check = nikStructural 64 Set₁ ({A : Set} → A → A)
