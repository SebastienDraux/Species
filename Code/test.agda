{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Fin

s : {A : Type₀} {x y : A} → x ≡ y → y ≡ x
s {A} {x} {y} p = subst (λ y → y ≡ x) p refl

0≠1 : ¬ (0 ≡ 1)
0≠1 p = subst (λ { zero → ℕ ; (suc n) → ⊥}) p 5

data 𝔹 : Type₁ where
  obj : ℕ → 𝔹
  hom : {m n : ℕ} → Fin m ≡ Fin n → obj m ≡ obj n
  hom-id : {n : ℕ} → hom (refl {x = Fin n}) ≡ refl
  hom-comp : {m n o : ℕ} (p : Fin m ≡ Fin n) (q : Fin n ≡ Fin o) → hom (p ∙ q) ≡ hom p ∙ hom q

-- rec : {A : 

lem : Σ ℕ (λ n → Fin n) ≃ 𝔹
lem = isoToEquiv i
  where
  i : Iso (Σ ℕ (λ n → Fin n)) 𝔹
  Iso.fun i (n , _) = obj n
  Iso.inv i b = {!!}
  Iso.rightInv i = {!!}
  Iso.leftInv i = {!!}

Species : {ℓ : Level} → Type (ℓ-suc ℓ)
Species {ℓ} = 𝔹 → Type ℓ
