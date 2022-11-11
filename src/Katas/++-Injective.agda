{-# OPTIONS --safe #-}
module Katas.++-Injective where

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.List.Properties
-- you can import other functions from the stdlib here

++-injectiveʳ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ b ≡ a ++ c → b ≡ c
++-injectiveʳ {_} {A} [] ys zs ab=ac = ab=ac
++-injectiveʳ {_} {A} (x ∷ xs) ys zs ab=ac rewrite ++-injectiveʳ xs ys zs (∷-injectiveʳ ab=ac) = refl

++-injectiveˡ-one : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) z →
  xs ++ z ∷ [] ≡ ys ++ z ∷ [] →
  xs ≡ ys
++-injectiveˡ-one [] [] z Heq = refl
++-injectiveˡ-one [] (x ∷ ys) z Heq with ++-conicalˡ ys (z ∷ []) (sym (∷-injectiveʳ Heq))
++-injectiveˡ-one [] (x ∷ []) z () | refl
++-injectiveˡ-one (x ∷ xs) [] z Heq with ++-conicalˡ xs (z ∷ []) (∷-injectiveʳ Heq)
++-injectiveˡ-one (x ∷ []) [] z () | refl
++-injectiveˡ-one (x ∷ xs) (y ∷ ys) z Heq rewrite ++-injectiveˡ-one _ _ _ (∷-injectiveʳ Heq) | ∷-injectiveˡ Heq = refl

-- pretty hard
-- try to use cong to convert to an eazier problem
++-injectiveˡ : ∀ {ℓ} {A : Set ℓ} (a b c : List A) → a ++ c ≡ b ++ c → a ≡ b
++-injectiveˡ xs ys [] ac=bc rewrite ++-identityʳ xs | ++-identityʳ ys = ac=bc
++-injectiveˡ xs ys (z ∷ zs) ac=bc rewrite sym (++-assoc xs (z ∷ []) zs) | sym (++-assoc ys (z ∷ []) zs) | ++-injectiveˡ-one xs ys z (++-injectiveˡ _ _ zs ac=bc) = refl
