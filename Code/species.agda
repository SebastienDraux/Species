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
open import finSet
open import B

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B C D : Type ℓ

Species : Type (ℓ-suc ℓ)
Species {ℓ = ℓ} = Σ[ X ∈ Type ℓ ] (X → FinSet)

Species' :  Type (ℓ-suc ℓ)
Species' {ℓ = ℓ} = FinSet → Type ℓ

species≃species' : Species ≃ Species'
species≃species' = equivClassification

--powerSeries : Type₁
--powerSeries = ℕ → Type₀

--_+ₚ_ : powerSeries → powerSeries → powerSeries
--(f +ₚ g) n = (f n) ⊎ (g n)

--_×ₚ_ : powerSeries → powerSeries → powerSeries
--(f ×ₚ g) n = aux n 0
--  where
--  aux : ℕ → ℕ → Type₀
--  aux zero l = (f 0) × (g l)
--  aux (suc k) l = (aux k (suc l)) ⊎ ((f (suc k)) × (g l))

--powerSeriesSpecies : Species → powerSeries
--powerSeriesSpecies (X , f) n = fiber (card ∘ f) n

--_+ₛ_ : Species → Species → Species
--(X , f) +ₛ (Y , g) = (X ⊎ Y) , (λ { (inl x) → f x ; (inr y) → g y})

--+-PSS : {f g : Species} → (powerSeriesSpecies f) +ₚ (powerSeriesSpecies g) ≡ powerSeriesSpecies (f +ₛ g)
--+-PSS {X , f} {Y , g} = funExt λ n → aux n
--  where
--  aux : (n : ℕ) → (powerSeriesSpecies (X , f) +ₚ powerSeriesSpecies (Y , g)) n ≡ powerSeriesSpecies ((X , f) +ₛ (Y , g)) n
--  aux n = ua (isoToEquiv i)
--
--    where
--    i : Iso ((powerSeriesSpecies (X , f) +ₚ powerSeriesSpecies (Y , g)) n) (powerSeriesSpecies ((X , f) +ₛ (Y , g)) n)
--    Iso.fun i (inl (x , p)) = inl x , p
--    Iso.fun i (inr (y , p)) = inr y , p
--    Iso.inv i (inl x , p) = inl (x , p)
--    Iso.inv i (inr y , p) = inr (y , p)
--    Iso.rightInv i (inl x , p) = refl
--    Iso.rightInv i (inr y , p) = refl
--    Iso.leftInv i (inl (x , p)) = refl
--   Iso.leftInv i (inr (y , p)) = refl

--_∙ₛ_ : Species → Species → Species
--(X , f) ∙ₛ (Y , g) = X × Y , λ { (x , y) → (fst (f x) ⊎ fst (g y)) , (fst (snd (f x)) + fst (snd (g y)) , ∣ ua (isoToEquiv (i x y)) ∣)}
--  where
 -- i : (x : X) → (y : Y) → Iso (fst (f x) ⊎ fst (g y)) (Fin (fst (snd (f x)) + fst (snd (g y))))
 -- i x y = j
--
 --   where
 --   j : Iso (fst (f x) ⊎ fst (g y)) (Fin (fst (snd (f x)) + fst (snd (g y))))
 --   Iso.fun j (inl x') = {!!} , {!!} , {!!}
 --   Iso.fun j (inr y') = {!!}
 --   Iso.inv j = {!!}
 --   Iso.rightInv j = {!!}
 --   Iso.leftInv j = {!!}


