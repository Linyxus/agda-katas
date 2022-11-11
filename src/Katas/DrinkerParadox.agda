{-# OPTIONS --safe #-}

open import Level
open import Axiom.ExcludedMiddle

module Katas.DrinkerParadox (em : ∀ {ℓ : Level} → ExcludedMiddle ℓ) where

open import Data.Product
open import Data.Empty
open import Relation.Unary
open import Relation.Nullary

paradox : ∀ {ℓ : Level} {A : Set ℓ} {r : Pred A ℓ} →
  (e : A) →
  ∃[ x ] (r x -> ∀ {y : A} -> r y)
paradox {_} {A} {r} e = H
  where
  exists-neg-r-dec : Dec (∃[ x ] ¬ r x)
  exists-neg-r-dec = em

  Hdec : ∀ x → Dec (r x)
  Hdec x = em

  Hall : ∀ (x : A) → ¬ (∃[ x ] ¬ r x) → (∀ y → r y)
  Hall x nex y with Hdec y
  ... | yes rx = rx
  ... | no nrx = ⊥-elim (nex (y , nrx))

  H : ∃[ x ] (r x -> ∀ {y : A} -> r y)
  H with exists-neg-r-dec
  ... | yes (x , Hx) = x , (λ rx → ⊥-elim (Hx rx))
  ... | no nex-neg = e , λ _ {y} → (Hall e nex-neg y)

