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
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Core.Primitives

-- exercice : trouver une preuve avec les indices
--substCompᵣ : {ℓ : Level} {A : Type ℓ} {x y y' : A} (q : y ≡ y') (p : x ≡ y) → subst (λ y → x ≡ y) q p ≡ p ∙ q
--substCompᵣ {x = x} q p = J (λ y' q → subst (λ y → x ≡ y) q p ≡ p ∙ q) (substRefl {B = λ y → x ≡ y} p ∙ rUnit p) q

--substCompₗ : {ℓ : Level} {A : Type ℓ} {x x' y : A} (q : x ≡ x') (p : x ≡ y) → subst (λ x → x ≡ y) q p ≡ (sym q) ∙ p
--substCompₗ {y = y} q p = J ((λ x' q → subst (λ x → x ≡ y) q p ≡ (sym q) ∙ p)) (substRefl {B = (λ x → x ≡ y)} p ∙ lUnit p) q

--Remplace substComp
subst≡ᵣ : {ℓ : Level} {A : Type ℓ} {x y : A} {a : A} (p : x ≡ y) (q : a ≡ x) → subst (λ x → a ≡ x) p q ≡ q ∙ p
subst≡ᵣ p q = fromPathP (compPath-filler q p)

subst≡ₗ : {ℓ : Level} {A : Type ℓ} {x y : A} {a : A} (p : x ≡ y) (q : x ≡ a) → subst (λ x → x ≡ a) p q ≡ (sym p) ∙ q
subst≡ₗ p q = fromPathP (compPath-filler' (sym p) q)

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
      subst (λ A → A ≡ Fin n) (sym p) refl ≡⟨ subst≡ₗ (sym p) refl ⟩
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
lem-4-8-2 {A} {B} f = compEquiv Σ-comm (lem-3-11-9-i λ a → (f a , refl) , (λ { (b , p) → (snd (isContrSingl (f a))) (b , p)}))

lem-2-9-4 : {ℓ ℓ' : Level} {X : Type ℓ} (A B : X → Type ℓ') {x y : X} (p : x ≡ y) (f : A x → B x) →
            subst (λ x → A x → B x) p f ≡ subst B p ∘ f ∘ subst A (sym p)
lem-2-9-4 A B p f = refl

equivalence : {B : Type₀} → (Σ[ X ∈ Type₀ ] (X → B)) ≃ (B → Type₀)
equivalence {B} = isoToEquiv i
  where
  i : Iso (Σ[ X ∈ Type₀ ]  (X → B)) (B → Type₀)
  Iso.fun i (X , f) = fiber f 
  Iso.inv i F = Σ B (λ b → F b) , fst
  Iso.rightInv i F = funExt (λ b → ua (isoToEquiv (i' b)))
    where
    i' : (b : B) → Iso (fiber fst b) (F b)
    -- i' b = iso (λ { ((b' , a') , p) → subst F p a'})
               -- (λ a → (b , a) , refl)
               -- (λ a → substRefl {B = F} a)
               -- (λ { ((b' , a') , p) → ΣPathP (ΣPathP (sym p , {!!}) , {!!}) })
    Iso.fun (i' b) ((b' , a') , p) = subst F p a'
    Iso.inv (i' b) a = (b , a) , refl
    Iso.rightInv (i' b) a = substRefl {B = F} a
    Iso.leftInv (i' b) ((b' , a') , p) = ΣPathP (ΣPathP (sym p , toPathP aux) , toPathP aux')
      where
      aux : transport (cong F (sym p)) (subst F p a') ≡ a'
      aux =
        transport (cong F (sym p)) (subst F p a') ≡⟨ refl ⟩
        subst F (sym p) (subst F p a')            ≡⟨ sym (substComposite F p (sym p) a') ⟩
        subst F (p ∙ sym p) a'                    ≡⟨ cong (λ p → subst F p a') (rCancel p) ⟩
        subst F refl a'                           ≡⟨ substRefl {B = F} a' ⟩
        a'                                        ∎
      auxP : PathP (λ i → cong F (sym p) i) (subst F p a') a'
      auxP = toPathP aux
      aux' =
        transport (λ i → fst (ΣPathP {B = λ _ → F} (sym p , auxP) i) ≡ b) refl ≡⟨ refl ⟩
        transport (λ i → sym p i ≡ b) refl ≡⟨ subst≡ₗ (sym p) refl ⟩
        p ∙ refl ≡⟨ sym (rUnit p) ⟩
        p ∎

  Iso.leftInv i (A , f) = ΣPathP (ua (lem-4-8-2 f) , toPathP aux)
    where
    aux =
      transport (λ i → ua (lem-4-8-2 f) i → B) fst ≡⟨ refl ⟩
      subst (λ X → X → B) (ua (lem-4-8-2 f)) fst ≡⟨ lem-2-9-4 (λ X → X) (λ _ → B) (ua (lem-4-8-2 f)) fst ⟩
      subst (λ _ → B) (ua (lem-4-8-2 f)) ∘ fst ∘ subst (λ X → X) (sym (ua (lem-4-8-2 f))) ≡⟨ cong (λ g → g ∘ fst ∘ subst (λ X → X) (sym (ua (lem-4-8-2 f)))) (funExt transportRefl) ⟩
      fst ∘ subst (λ X → X) (sym (ua (lem-4-8-2 f))) ≡⟨ refl ⟩
      fst ∘ transport (sym (ua (lem-4-8-2 f))) ≡⟨ cong (λ p → fst ∘ (transport p)) (sym (uaInvEquiv (lem-4-8-2 f))) ⟩
      fst ∘ transport (ua (invEquiv (lem-4-8-2 f))) ≡⟨ funExt (λ x → cong (λ y → fst y) (uaβ ((invEquiv (lem-4-8-2 f))) x)) ⟩
      fst ∘ equivFun (invEquiv (lem-4-8-2 f)) ≡⟨ refl ⟩
      f ∎
