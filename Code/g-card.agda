{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Core.Primitives
open import Cubical.HITs.PropositionalTruncation renaming (rec to trunc-rec)
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat.Order

open import lemma

module g-card where

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B C D : Type ℓ

postulate

  g-card : Type ℓ → ℕ
  g-card-Unit : g-card Unit ≡ 1
  g-card-equiv : ∥ A ≃ B ∥ → g-card A ≡ g-card B
  g-card-⊎ : g-card (A ⊎ B) ≡ g-card A + g-card B
  --g-card-fiber : {!!}

g-card-⊥ : g-card ⊥ ≡ 0
g-card-⊥ = m+n≡n→m≡0 (sym (p ∙ +-comm 1 (g-card ⊥)))
  where
  p =
    1 ≡⟨ sym g-card-Unit ⟩
    g-card Unit ≡⟨ g-card-equiv ∣ invEquiv ⊎-⊥-≃ ∣ ⟩
    g-card (Unit ⊎ ⊥) ≡⟨ g-card-⊎ ⟩
    (g-card Unit) + (g-card ⊥) ≡⟨ cong (λ n → n + (g-card ⊥)) g-card-Unit ⟩
    1 + (g-card ⊥) ∎

g-card-Aut-⊥ : (g-card (Aut ⊥)) ≡ 1
g-card-Aut-⊥ = 
  g-card (Aut ⊥) ≡⟨ g-card-equiv ∣ Aut-⊥ ∣ ⟩
  g-card Unit ≡⟨ g-card-Unit ⟩
  1 ∎
  
g-card-Aut-Unit : (g-card (Aut Unit)) ≡ 1
g-card-Aut-Unit = 
  g-card (Aut Unit) ≡⟨ g-card-equiv ∣ Aut-Unit ∣ ⟩
  g-card Unit ≡⟨ g-card-Unit ⟩
  1 ∎
