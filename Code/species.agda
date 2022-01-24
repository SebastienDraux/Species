{-# OPTIONS --cubical #-}

open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin

-- exercice : trouver une preuve avec les indices
substComp : {ℓ : Level} {A : Type ℓ} {x y y' : A} (q : y ≡ y') (p : x ≡ y) → subst (λ y → x ≡ y) q p ≡ p ∙ q
substComp {x = x} q p = J (λ y' q → subst (λ y → x ≡ y) q p ≡ p ∙ q) (substRefl {B = λ y → x ≡ y} p ∙ rUnit p) q

lem : Σ Type₀ (λ A → Σ ℕ (λ n → A ≡ Fin n)) ≃ ℕ
lem = isoToEquiv i
  where
  i : Iso (Σ Type₀ (λ A → Σ ℕ (λ n → A ≡ Fin n))) ℕ
  Iso.fun i (A , n , p) = n
  Iso.inv i n = Fin n , n , refl
  Iso.rightInv i n = refl
  Iso.leftInv i (A , n , p) = ΣPathP (sym p , toPathP (ΣPathP (refl , test)))
    where
    test =
      subst (λ A → A ≡ Fin n) (sym p) refl ≡⟨ {!!} ⟩
      sym (sym p) ≡⟨ {!!} ⟩
      p ∎

lem-3-11-9-i : {A : Type₀} → {P : A → Type₀} → ((a : A) → isContr (P a)) → (Σ A P) ≃ A
lem-3-11-9-i {A} {P} c = isoToEquiv i
  where
  i : Iso (Σ A P) A
  Iso.fun i (a , _) = a
  Iso.inv i a = (a , fst (c a))
  Iso.rightInv i a = refl
  Iso.leftInv i (a , pa) = ΣPathP (refl , snd (c a) pa)

-- NB: singl / contrSingl
Σ-id-contr : {A : Type₀} → {a : A} → isContr (Σ A (a ≡_ ))
Σ-id-contr {a = a} = ((a , refl) , λ { (b , p) → ΣPathP (p , λ i j → p (i ∧ j))})
-- Σ-id-contr {A} {a} = (a , refl) , (λ { (a' , a≡a') → ΣPathP (a≡a' , toPathP (lem a' a≡a')) })
  -- where
  -- lem = λ (a' : A) (a≡a' : a ≡ a') →
    -- subst (λ a' → a ≡ a') a≡a' refl ≡⟨ {!!} ⟩
    -- a≡a' ∎

Σ-comm : {A B : Type₀} → {P : A → B → Type₀} → Σ A (λ a → (Σ B (λ b → P a b))) ≃ Σ B (λ b → (Σ A (λ a → P a b)))
Σ-comm {A = A} {B = B} {P = P} = isoToEquiv i
  where
  i : Iso (Σ A (λ a → (Σ B (λ b → P a b)))) (Σ B (λ b → (Σ A (λ a → P a b))))
  Iso.fun i (a , b , pab) = (b , (a , pab))
  Iso.inv i (b , a , pab) = (a , (b , pab))
  Iso.rightInv i _ = refl
  Iso.leftInv i _ = refl

lem-4-8-2 : {A B : Type₀} → (f : A → B) → Σ B (fiber f) ≃ A
lem-4-8-2 {A} {B} f = compEquiv Σ-comm (lem-3-11-9-i λ _ → Σ-id-contr)

--test : {A : Set} → (c : isContr A) → sym ((snd c) (fst c)) ≡ refl
--test c = (isProp→isSet (isContr→isProp c) (fst c) (fst c)) (sym (snd c (fst c))) refl

--lem-3-11-9-ii : {A : Type₀} → (P : A → Type₀) → (c : isContr A) → Σ A P ≃ P (fst c)
--lem-3-11-9-ii {A = A} P c = isoToEquiv i
--  where
--  i : Iso (Σ A P) (P (fst c))
--  Iso.fun i (a , pa) = subst P (sym ((snd c) a)) pa
--  Iso.inv i pa = (fst c , pa)
--  Iso.rightInv i x = cong (λ p → subst P  p x) (test c) ∙ (substRefl x)
--  Iso.leftInv i (a , pa) = ΣPathP ((snd c) a , {!!})


--lem-482 : {A B : Type₀} → (f : A → B) → A ≃ Σ B (fiber f)

equivalence : {B : Type₀} → Σ Type₀ (λ A → A → B) ≃ B → Type₀
equivalence = {!!}
