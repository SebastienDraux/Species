{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import lemma
open import finSet

module B where

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B C D : Type ℓ

data 𝔹 : Type₁ where
  obj : ℕ → 𝔹
  hom : {m n : ℕ} → Fin m ≡ Fin n → obj m ≡ obj n
  hom-id : {n : ℕ} → hom (refl {x = Fin n}) ≡ refl
  hom-comp : {m n o : ℕ} (p : Fin m ≡ Fin n) (q : Fin n ≡ Fin o) → hom (p ∙ q) ≡ hom p ∙ hom q

--𝔹toℕ : 𝔹 → ℕ
--𝔹toℕ (obj n) = n
--𝔹toℕ (hom {m = m} {n = n} p i) = (injFin m n (pathToEquiv p)) i
--𝔹toℕ (hom-id {n = n} i j) = aux i j
--  where
--  aux =
--    injFin  n n (pathToEquiv refl) ≡⟨ cong (λ f → injFin n n f) pathToEquivRefl ⟩
--    injFin n n (idEquiv (Fin n)) ≡⟨ injFinId n ⟩
--    refl ∎
--𝔹toℕ (hom-comp {m = m} {n = n} {o = o} p q i j) = aux i j
--  where
--  aux = 
--    injFin m o (pathToEquiv (p ∙ q)) ≡⟨ cong (λ p → injFin m o p) (sym (compEquivPathToEquiv p q)) ⟩
--    injFin m o (compEquiv (pathToEquiv p) (pathToEquiv q)) ≡⟨ {!!} ⟩
--    (injFin m n (pathToEquiv p)) ∙ (injFin n o (pathToEquiv q)) ∎

--𝔹-rec : isGroupoid A → (f : ℕ → A) → (F : {m n : ℕ} → Fin m ≡ Fin n → f m ≡ f n) → ({n : ℕ} → F (refl {x = Fin n}) ≡ refl) → ({m n o : ℕ} → (p : Fin m ≡ Fin n) → (q : Fin n ≡ Fin o) → F (p ∙ q) ≡ (F p) ∙ (F q)) → (𝔹 → A)
--𝔹-rec grp f F idF compF (obj n) = f n
--𝔹-rec grp f F idF compF (hom p i) = F p i
--𝔹-rec grp f F idF compF (hom-id {n = n} i j) = idF {n = n} i j
--𝔹-rec grp f F idF compF (hom-comp {m = m} {n = n} {o = o} p q i j) = {!!}

postulate
  𝔹toℕ : 𝔹 → ℕ
  𝔹toℕ-obj : (n : ℕ) → 𝔹toℕ (obj n) ≡ n
