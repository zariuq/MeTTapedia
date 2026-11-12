{-# OPTIONS --safe --without-K #-}
module DefinedHead where
open import NikStructuralExport
open import Agda.Builtin.Unit
identity : (A : Set) → A → A
identity A x = x
check : ⊤
check = nikStructural 64 ((A : Set) → A → A) identity
