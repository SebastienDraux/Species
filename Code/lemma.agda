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

open import Cubical.Data.Sigma renaming (_×_ to _×Σ_)
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Core.Primitives
open import Cubical.HITs.PropositionalTruncation renaming (rec to trunc-rec)
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat.Order
open import Cubical.Functions.Embedding

module lemma where

private
  variable
    ℓ ℓ' ℓ''  : Level
    A B C D : Type ℓ

subst≡ᵣ : {x y : A} {a : A} (p : x ≡ y) (q : a ≡ x) → subst (λ x → a ≡ x) p q ≡ q ∙ p
subst≡ᵣ p q = fromPathP (compPath-filler q p)

subst≡ₗ : {x y : A} {a : A} (p : x ≡ y) (q : x ≡ a) → subst (λ x → x ≡ a) p q ≡ (sym p) ∙ q
subst≡ₗ p q = fromPathP (compPath-filler' (sym p) q)

lem-3-11-9-i : {P : A → Type ℓ'} → ((a : A) → isContr (P a)) → (Σ A P) ≃ A
lem-3-11-9-i {A = A} {P = P} c = isoToEquiv i
  where
  i : Iso (Σ A P) A
  Iso.fun i (a , _) = a
  Iso.inv i a = (a , fst (c a))
  Iso.rightInv i a = refl
  Iso.leftInv i (a , pa) = ΣPathP (refl , snd (c a) pa)

Σ-comm : {P : A → B → Type ℓ'} → (Σ[ a ∈ A ] (Σ[ b ∈ B ] P a b)) ≃ (Σ[ b ∈ B ] (Σ[ a ∈ A ] P a b))
Σ-comm {A = A} {B = B} {P = P} = isoToEquiv i
  where
  i : Iso (Σ[ a ∈ A ] (Σ[ b ∈ B ] P a b)) (Σ[ b ∈ B ] (Σ[ a ∈ A ] P a b))
  Iso.fun i (a , b , pab) = (b , (a , pab))
  Iso.inv i (b , a , pab) = (a , (b , pab))
  Iso.rightInv i _ = refl
  Iso.leftInv i _ = refl

lem-4-8-2 : (f : A → B) → Σ B (fiber f) ≃ A
lem-4-8-2 {A = A} {B} f = compEquiv Σ-comm (lem-3-11-9-i λ a → (f a , refl) , (λ { (b , p) → (snd (isContrSingl (f a))) (b , p)}))

lem-2-9-4 : {X : Type ℓ} (A B : X → Type ℓ') {x y : X} (p : x ≡ y) (f : A x → B x) →
            subst (λ x → A x → B x) p f ≡ subst B p ∘ f ∘ subst A (sym p)
lem-2-9-4 A B p f = refl

equivClassification : {B : Type₁} → (Σ[ X ∈ Type₁ ] (X → B)) ≃ (B → Type₁)
equivClassification {B = B} = isoToEquiv i
  where
  i : Iso (Σ[ X ∈ Type₁ ]  (X → B)) (B → Type₁)
  Iso.fun i (X , f) = fiber f 
  Iso.inv i F = Σ B F , fst
  Iso.rightInv i F = funExt (λ b → ua (isoToEquiv (i' b)))
    where
    i' : (b : B) → Iso (fiber fst b) (F b)
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

inl≠inr : (a : A) → (b : B) → ((inl a ≡ inr b) → ⊥)
inl≠inr {A = A} {B = B} a b p = znots (cong f p)
  where
  f : A ⊎ B → ℕ
  f (inl a) = 0
  f (inr b) = 1

inj-inl : {a a' : A} → inl {B = B} a ≡ inl {B = B} a' → a ≡ a'
inj-inl {a = a} {a' = a'} p i = fst (((isEmbedding→hasPropFibers isEmbedding-inl) (inl a)) (a , refl) (a' , sym p) i)

inj-inr : {b b' : B} → inr {A = A} b ≡ inr {A = A} b' → b ≡ b'
inj-inr {b = b} {b' = b'} p i = fst (((isEmbedding→hasPropFibers isEmbedding-inr) (inr b)) (b , refl) (b' , sym p) i)

inj-⊎-Unit : (A ⊎ Unit) ≃ (B ⊎ Unit) → A ≃ B
inj-⊎-Unit {A = A} {B = B} e = isoToEquiv i
  where
  f = Iso.fun (equivToIso e)
  g = Iso.inv (equivToIso e)
  rinv = Iso.leftInv (equivToIso e)
  linv = Iso.rightInv (equivToIso e)
  i : Iso A B
  Iso.fun i a with isContrSingl (f (inl a)) | isContrSingl (f (inr tt))
  ... | (inl b , p) , _ | _ = b
  ... | (inr tt , p) , _ | (inl b , q) , _ = b
  ... | (inr tt , p) , _ | (inr tt , q) , _ = ⊥-rec (inl≠inr a tt (sym (rinv (inl a)) ∙ cong g (p ∙ (sym q)) ∙ (rinv (inr tt))))
  Iso.inv i b with isContrSingl (g (inl b)) | isContrSingl (g (inr tt))
  ... | (inl a , p) , _ | _ = a
  ... | (inr tt , p) , _ | (inl a , q) , _ = a
  ... | (inr tt , p) , _ | (inr tt , q) , _ = ⊥-rec (inl≠inr b tt (sym (linv (inl b)) ∙ cong f (p ∙ (sym q)) ∙ linv (inr tt)))
  Iso.leftInv i a with isContrSingl (f (inl a)) | isContrSingl (f (inr tt)) | isContrSingl (g (inl b)) | isContrSingl (g (inr tt))
    where b = (Iso.fun i) a
  ... | (inl b' , p) , _ | _ | (inl a' , p') , _ | _ = sym (inj-inl (sym (rinv (inl a)) ∙ (cong g p) ∙ p'))
  ... | (inl b' , p) , _ | _ | (inr tt , p') , _ | (inl a' , q') , _ = ⊥-rec (inl≠inr a tt (sym (rinv (inl a)) ∙ cong g p ∙ p'))
  ... | (inl b' , p) , _ | _ | (inr tt , p') , _ | (inr tt , q') , _ = ⊥-rec (inl≠inr b' tt (sym (linv (inl b')) ∙ cong f p' ∙ sym (cong f q') ∙ linv (inr tt)))
  ... | (inr tt , p) , _ | (inl b' , q) , _ | (inl a' , p') , _ | _ = ⊥-rec (inl≠inr a' tt (sym p' ∙ cong g (sym q) ∙ rinv (inr tt)))
  ... | (inr tt , p) , _ | (inl b' , q) , _ | (inr tt , p') , _ | (inl a' , q') , _ = sym (inj-inl (sym (rinv (inl a)) ∙ cong g p ∙ q'))
  ... | (inr tt , p) , _ | (inl b' , q) , _ | (inr tt , p') , _ | (inr tt , q') , _ = ⊥-rec (inl≠inr b' tt (sym (linv (inl b')) ∙ cong f p' ∙ cong f (sym q') ∙ linv (inr tt)))
  ... | (inr tt , p) , _ | (inr tt , q) , _ | _ | _ = ⊥-rec (⊥-rec (inl≠inr a tt ( sym (rinv (inl a)) ∙ cong g (p ∙ (sym q)) ∙ rinv (inr tt))))
  
  Iso.rightInv i b with isContrSingl (g (inl b)) | isContrSingl (g (inr tt)) | isContrSingl (f (inl a)) | isContrSingl (f (inr tt))
    where a = (Iso.inv i) b
  ... | (inl a' , p) , _ | _ | (inl b' , p') , _ | _ = sym (inj-inl (sym (linv (inl b)) ∙ cong f p ∙ p'))
  ... | (inl a' , p) , _ | _ | (inr tt , p') , _ | (inl b' , q') , _ = ⊥-rec (inl≠inr b tt (sym (linv (inl b)) ∙ cong f p ∙ p'))
  ... | (inl a' , p) , _ | _ | (inr tt , p') , _ | (inr tt , q') , _ = ⊥-rec (inl≠inr a' tt (sym (rinv (inl a')) ∙ cong g (p' ∙ (sym q')) ∙ (rinv (inr tt))))
  ... | (inr tt , p) , _ | (inl a' , q) , _ | (inl b' , p') , _ | _ = ⊥-rec (inl≠inr b' tt (sym p' ∙ cong f (sym q) ∙ linv (inr tt)))
  ... | (inr tt , p) , _ | (inl a' , q) , _ | (inr tt , p') , _ | (inl b' , q') , _ = inj-inl (sym (sym (linv (inl b)) ∙ cong f p ∙ q'))
  ... | (inr tt , p) , _ | (inl a' , q) , _ | (inr tt , p') , _ | (inr tt , q') , _  = ⊥-rec (inl≠inr a' tt (sym (rinv (inl a')) ∙ cong g p' ∙ cong g (sym q') ∙ rinv (inr tt)))
  ... | (inr tt , p) , _ | (inr tt , q) , _ | _ | _ = ⊥-rec (inl≠inr b tt (sym (linv (inl b)) ∙ cong f (p ∙ (sym q)) ∙ linv (inr tt)))

inj-⊎-Unit-Id : inj-⊎-Unit (idEquiv (A ⊎ Unit)) ≡ idEquiv A
inj-⊎-Unit-Id {A = A} = equivEq (funExt aux)
  where
  f = equivFun (inj-⊎-Unit (idEquiv (A ⊎ Unit)))
  aux : (a : A) → f a ≡ a
  aux a = refl
  
∥compEquiv∥ : ∥ A ≃ B ∥ → ∥ B ≃ C ∥ → ∥ A ≃ C ∥
∥compEquiv∥ = map2 compEquiv

⊎Equiv : A ≃ B → C ≃ D → A ⊎ C ≃ B ⊎ D
⊎Equiv equiv equiv' = isoToEquiv (⊎Iso (equivToIso equiv) (equivToIso equiv'))

∥⊎Equiv∥ : ∥ A ≃ B ∥ → ∥ C ≃ D ∥ → ∥ (A ⊎ C) ≃ (B ⊎ D) ∥
∥⊎Equiv∥ = map2 ⊎Equiv

∥pathToEquiv∥ : ∥ A ≡ B ∥ → ∥ A ≃ B ∥
∥pathToEquiv∥ = trunc-rec isPropPropTrunc λ p → ∣ pathToEquiv p ∣

∥ua∥ : ∥ A ≃ B ∥ → ∥ A ≡ B ∥
∥ua∥ = trunc-rec isPropPropTrunc λ p → ∣ ua p ∣

×-⊥-≃ : A × ⊥ ≃ ⊥
×-⊥-≃ {A = A} = isoToEquiv i
  where
  i : Iso (A × ⊥) ⊥
  Iso.fun i (a , ())
  Iso.inv i ()
  Iso.leftInv i (a , ())
  Iso.rightInv i ()

×-Unit-≃ : A × Unit ≃ A
×-Unit-≃ {A = A} = isoToEquiv i
  where
  i : Iso (A × Unit) A
  Iso.fun i (a , tt) = a
  Iso.inv i a = a , tt
  Iso.leftInv i (a , tt) = refl
  Iso.rightInv i a = refl

⊎-×-distrib : (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
⊎-×-distrib {A = A} {B = B} {C = C} = isoToEquiv i
  where
  i : Iso ((A ⊎ B) × C) ((A × C) ⊎ (B × C))
  Iso.fun i (inl a , c) = inl (a , c)
  Iso.fun i (inr b , c) = inr (b , c)
  Iso.inv i (inl (a , c)) = (inl a) , c
  Iso.inv i (inr (b , c)) = (inr b) , c
  Iso.leftInv i (inl a , c) = refl
  Iso.leftInv i (inr b , c) = refl
  Iso.rightInv i (inl (a , c)) = refl
  Iso.rightInv i (inr (b , c)) = refl

∥×-≃∥ : ∥ A ≃ C ∥ → ∥ B ≃ D ∥ → ∥ A × B ≃ C × D ∥
∥×-≃∥ = map2 ×-≃

compEquivPathToEquiv : (p : A ≡ B) → (q : B ≡ C) → compEquiv (pathToEquiv p) (pathToEquiv q) ≡ pathToEquiv (p ∙ q)
compEquivPathToEquiv p q = 
  compEquiv (pathToEquiv p) (pathToEquiv q) ≡⟨ refl ⟩
  compEquiv e f ≡⟨ sym (pathToEquiv-ua (compEquiv e f)) ⟩
  pathToEquiv (ua (compEquiv e f)) ≡⟨ cong pathToEquiv (uaCompEquiv e f) ⟩
  pathToEquiv ((ua e) ∙ (ua f)) ≡⟨ cong (λ p → pathToEquiv (p ∙ (ua f))) (ua-pathToEquiv p) ⟩
  pathToEquiv (p ∙ (ua f))≡⟨  cong (λ q → pathToEquiv (p ∙ q)) (ua-pathToEquiv q) ⟩
  pathToEquiv (p ∙ q) ∎

  where
  e = pathToEquiv p
  f = pathToEquiv q
