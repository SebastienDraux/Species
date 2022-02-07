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
open import Cubical.Foundations.Univalence
open import Cubical.Core.Primitives

-- exercice : trouver une preuve avec les indices
substCompᵣ : {ℓ : Level} {A : Type ℓ} {x y y' : A} (q : y ≡ y') (p : x ≡ y) → subst (λ y → x ≡ y) q p ≡ p ∙ q
substCompᵣ {x = x} q p = J (λ y' q → subst (λ y → x ≡ y) q p ≡ p ∙ q) (substRefl {B = λ y → x ≡ y} p ∙ rUnit p) q

substCompₗ : {ℓ : Level} {A : Type ℓ} {x x' y : A} (q : x ≡ x') (p : x ≡ y) → subst (λ x → x ≡ y) q p ≡ (sym q) ∙ p
substCompₗ {y = y} q p = J ((λ x' q → subst (λ x → x ≡ y) q p ≡ (sym q) ∙ p)) (substRefl {B = (λ x → x ≡ y)} p ∙ lUnit p) q

--subst≡ᵣ : {ℓ : Level} {A : Type ℓ} {x y : A} (a : A) (p : x ≡ y) (q : a ≡ x) → subst (λ x → a ≡ x) p q ≡ q ∙ p
--subst≡ᵣ a p q = fromPathP (compPath-filler q p)

lem : (Σ[ A ∈ Type₀ ] (Σ[ n ∈ ℕ ] (A ≡ Fin n))) ≃ ℕ
lem = isoToEquiv i
  where
  i : Iso (Σ[ A ∈ Type₀ ] (Σ[ n ∈ ℕ ] (A ≡ Fin n))) ℕ
  Iso.fun i (A , n , p) = n
  Iso.inv i n = Fin n , n , refl
  Iso.rightInv i n = refl
  Iso.leftInv i (A , n , p) = ΣPathP (sym p , toPathP (ΣPathP (refl , test)))
    where
    test =
      subst (λ A → A ≡ Fin n) (sym p) refl ≡⟨ substCompₗ (sym p) refl ⟩
      (sym (sym p)) ∙ refl ≡⟨ sym (rUnit (sym (sym p))) ⟩
      sym (sym p) ≡⟨ refl ⟩
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
-- Σ-id-contr : {A : Type₀} → {a : A} → isContr (Σ A (a ≡_ ))
-- Σ-id-contr {a = a} = ((a , refl) , λ { (b , p) → ΣPathP (p , λ i j → p (i ∧ j))})
-- Σ-id-contr {A} {a} = (a , refl) , (λ { (a' , a≡a') → ΣPathP (a≡a' , toPathP (lem a' a≡a')) })
  -- where
  -- lem = λ (a' : A) (a≡a' : a ≡ a') →
    -- subst (λ a' → a ≡ a') a≡a' refl ≡⟨ {!!} ⟩
    -- a≡a' ∎

Σ-comm : {A B : Type₀} → {P : A → B → Type₀} → (Σ[ a ∈ A ] (Σ[ b ∈ B ] P a b)) ≃ (Σ[ b ∈ B ] (Σ[ a ∈ A ] P a b))
Σ-comm {A = A} {B = B} {P = P} = isoToEquiv i
  where
  i : Iso (Σ[ a ∈ A ] (Σ[ b ∈ B ] P a b)) (Σ[ b ∈ B ] (Σ[ a ∈ A ] P a b))
  Iso.fun i (a , b , pab) = (b , (a , pab))
  Iso.inv i (b , a , pab) = (a , (b , pab))
  Iso.rightInv i _ = refl
  Iso.leftInv i _ = refl

lem-4-8-2 : {A B : Type₀} → (f : A → B) → Σ B (fiber f) ≃ A
lem-4-8-2 {A} {B} f = compEquiv Σ-comm (lem-3-11-9-i λ a → (f a , refl) , (λ { (b , p) → contrSingl p}))

equivalence : {B : Type₀} → (Σ[ X ∈ Type₀ ]  (X → B)) ≃ (B → Type₀)
equivalence {B} = isoToEquiv i
  where
  i : Iso (Σ[ X ∈ Type₀ ]  (X → B)) (B → Type₀)
  Iso.fun i (X , f) = fiber f 
  Iso.inv i F = (Σ B (λ b → F b)) , fst
  Iso.rightInv i F = funExt λ b → ua (isoToEquiv (i' b))
    where
    i' : (b : B) → Iso (fiber fst b) (F b)
    i' b = iso (λ { ((b' , a') , p) → subst F p a'})
               (λ a → (b , a) , refl)
               (λ a → substRefl {B = F} a)
               (λ { ((b' , a') , p) → ΣPathP (ΣPathP (sym p , {!!}) , {!!}) })
               
  --Iso.leftInv i (A , f) = ΣPathP (ua (lem-4-8-2 f) , {!!})
  Iso.leftInv i (A , f) = sigmaPath→pathSigma ((Σ B (fiber f) , fst)) (A , f) ((ua (lem-4-8-2 f)) , funExt λ x → {!!})
