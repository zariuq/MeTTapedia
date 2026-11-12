{-# OPTIONS --safe --without-K #-}
module OpenContext where
open import NikStructuralExport
open import Agda.Builtin.Unit
check : Set → ⊤
check A = nikStructural 64 Set₁ Set
