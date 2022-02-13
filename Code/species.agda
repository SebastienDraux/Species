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

FinSet : Type₁
FinSet = Σ[ A ∈ Type₀ ] (Σ[ n ∈ ℕ ] ∥ A ≡ Fin n ∥)

card : FinSet → ℕ
card (A , n , _) = n

unitFS : FinSet
unitFS = Unit , (1 , ∣ ua (isoToEquiv i) ∣)
  where
  i : Iso Unit (Fin 1)
  Iso.fun i tt = 0 , (0 , refl)
  Iso.inv i (zero , ie) = tt
  Iso.inv i (suc n , k , p) = tt
  Iso.rightInv i (zero , zero , p) = λ i → 0 , (0 ,  ((isSetℕ 1 1) refl p) i)
  Iso.rightInv i (zero , suc k , p) = ⊥-rec (snotz (injSuc (cong suc (+-comm 1 k) ∙ p)))
  Iso.rightInv i (suc n , k , p) = ⊥-rec (snotz (injSuc ((cong suc (sym (+-suc k n)) ∙ sym (+-suc k (suc n))) ∙ p)))
  Iso.leftInv i tt = refl

emptyFS : FinSet
emptyFS = ⊥ , (0 , ∣ ua (isoToEquiv i) ∣)
  where
  i : Iso ⊥ (Fin 0)
  Iso.fun i ()
  Iso.inv i (n , k , p) = ⊥-rec (snotz (sym (+-suc k n) ∙ p))
  Iso.rightInv i (n , k , p) = ⊥-rec (Iso.inv i (n , k , p))
  Iso.leftInv i ()

claim-2-1 : card unitFS ≡ 1
claim-2-1 = refl

inj-Fin : {n m : ℕ} → ∥ Fin n ≃ Fin m ∥ → n ≡ m
inj-Fin {n} {m} = trunc-rec (isSetℕ n m) aux
  where
  aux : Fin n ≃ Fin m → n ≡ m
  aux equiv = {!!}
  
comp-∥≃∥ : {A B C : Type₀} → ∥ A ≃ B ∥ → ∥ B ≃ C ∥ → ∥ A ≃ C ∥
comp-∥≃∥ = map2 compEquiv

claim-2-2 : {A B : FinSet} → ∥ fst A ≃ fst B ∥ → card A ≡ card B
claim-2-2 {A , n , q} {B , m , q'} equiv = inj-Fin (comp-∥≃∥ (comp-∥≃∥ ((trunc-rec isPropPropTrunc (λ p → ∣ pathToEquiv (sym p) ∣) q)) equiv) (trunc-rec isPropPropTrunc (λ p → ∣ pathToEquiv p ∣) q'))

+-Fun : {n m : ℕ} → Fin (n + m) ≃ Fin n ⊎ Fin m
+-Fun {n} {m} = isoToEquiv i
  where
  i : Iso (Fin (n + m)) (Fin n ⊎ Fin m) 
  Iso.fun i (x , y , p) with x ≟ n
  ... | lt (k , p') = inl (x , k , p')
  ... | eq p' = inr (0 , y , inj-m+ equa)
    where
    equa : n + (y + 1) ≡ n + m
    equa =
      n + (y + 1) ≡⟨ cong (λ z → n + z) (+-comm y 1) ⟩
      n + suc y ≡⟨ cong (λ z → z + suc y) (sym p') ⟩
      x + suc y ≡⟨ +-suc x y ⟩
      suc (x + y) ≡⟨ refl ⟩
      suc x + y ≡⟨ +-comm (suc x) y ⟩
      y + suc x ≡⟨ p ⟩
      n + m ∎
  ... | gt (k , p') = inr (suc k , y , inj-m+ equa)
    where
      equa : n + (y + suc (suc k)) ≡ n + m
      equa =
        n + (y + suc (suc k)) ≡⟨ +-assoc n y (suc (suc k)) ⟩
        n + y + suc (suc k) ≡⟨ cong (λ z → z + suc (suc k)) (+-comm n y) ⟩
        y + n + suc (suc k) ≡⟨ sym (+-assoc y n (suc (suc k))) ⟩
        y + (n + suc (suc k)) ≡⟨ cong (λ z → y + z) (+-suc n (suc k)) ⟩
        y + suc (n + suc k) ≡⟨ cong (λ z → y + z) (+-comm (suc n) (suc k)) ⟩
        y + suc (k + suc n) ≡⟨ cong ((λ z → y + z) ∘ suc) p' ⟩
        y + suc x ≡⟨ p ⟩
        n + m ∎
  Iso.inv i (inl (x , y , p)) = x , y + m , sym (+-assoc y m (suc x)) ∙ cong (λ z → y + z) (+-comm m (suc x)) ∙ +-assoc y (suc x) m ∙ (cong (λ z → z + m) p)
  Iso.inv i (inr (x , y , p)) = x + n , y , +-assoc y (suc x) n ∙ cong (λ z → z + n) p ∙ +-comm m n
  Iso.rightInv i (inl (x , y , p)) = {!!}
  Iso.rightInv i (inr (x , y , p)) = {!!}
  Iso.leftInv i (x , y , p) with x ≟ n
  ... | lt (k , p') = λ j → x , (inj-m+ equa) j , {!!}
     where
     equa : suc x + (k + m) ≡ suc x + y
     equa =
       suc x + (k + m) ≡⟨ +-comm (suc x) (k + m) ⟩
       k + m + suc x ≡⟨ sym (+-assoc k m (suc x)) ⟩
       k + (m + suc x) ≡⟨ cong (λ z → k + z) (+-comm m (suc x)) ⟩
       k + (suc x + m) ≡⟨ +-assoc k (suc x) m ⟩
       k + suc x + m ≡⟨ cong (λ z → z + m) p' ⟩
       n + m ≡⟨ sym p ⟩
       y + suc x ≡⟨ +-comm y (suc x) ⟩
       suc x + y ∎
  ... | eq p' = λ j → p' (~ j) , y , {!!}
  ... | gt (k , p') = {!!}

⊎-∥∥-comp : {A B C D : Type₀} → ∥ A ≃ B ∥ → ∥ C ≃ D ∥ → ∥ (A ⊎ C) ≃ (B ⊎ D) ∥
⊎-∥∥-comp = map2 {!!}

_+ₙ_ : FinSet → FinSet → FinSet
(A , n , p) +ₙ (B , m , q) = (A ⊎ B) , (n + m , {!!})

Species : Type₁
Species = Σ[ X ∈ Type₀ ] (X → FinSet)

powerSeries : Type₁
powerSeries = ℕ → Type₀

_+ₚ_ : powerSeries → powerSeries → powerSeries
(f +ₚ g) n = (f n) ⊎ (g n)

_×ₚ_ : powerSeries → powerSeries → powerSeries
(f ×ₚ g) n = aux n 0
  where
  aux : ℕ → ℕ → Type₀
  aux zero l = (f 0) × (g l)
  aux (suc k) l = (aux k (suc l)) ⊎ ((f (suc k)) × (g l))

powerSeriesSpecies : Species → powerSeries
powerSeriesSpecies (X , f) n = fiber (card ∘ f) n

_+ₛ_ : Species → Species → Species
(X , f) +ₛ (Y , g) = (X ⊎ Y) , (λ { (inl x) → f x ; (inr y) → g y})

+-PSS : {f g : Species} → (powerSeriesSpecies f) +ₚ (powerSeriesSpecies g) ≡ powerSeriesSpecies (f +ₛ g)
+-PSS {X , f} {Y , g} = funExt λ n → aux n
  where
  aux : (n : ℕ) → (powerSeriesSpecies (X , f) +ₚ powerSeriesSpecies (Y , g)) n ≡ powerSeriesSpecies ((X , f) +ₛ (Y , g)) n
  aux n = ua (isoToEquiv i)

    where
    i : Iso ((powerSeriesSpecies (X , f) +ₚ powerSeriesSpecies (Y , g)) n) (powerSeriesSpecies ((X , f) +ₛ (Y , g)) n)
    Iso.fun i (inl (x , p)) = inl x , p
    Iso.fun i (inr (y , p)) = inr y , p
    Iso.inv i (inl x , p) = inl (x , p)
    Iso.inv i (inr y , p) = inr (y , p)
    Iso.rightInv i (inl x , p) = refl
    Iso.rightInv i (inr y , p) = refl
    Iso.leftInv i (inl (x , p)) = refl
    Iso.leftInv i (inr (y , p)) = refl

_∙ₛ_ : Species → Species → Species
(X , f) ∙ₛ (Y , g) = X × Y , λ { (x , y) → (fst (f x) ⊎ fst (g y)) , (fst (snd (f x)) + fst (snd (g y)) , ∣ ua (isoToEquiv (i x y)) ∣)}
  where
  i : (x : X) → (y : Y) → Iso (fst (f x) ⊎ fst (g y)) (Fin (fst (snd (f x)) + fst (snd (g y))))
  i x y = j

    where
    j : Iso (fst (f x) ⊎ fst (g y)) (Fin (fst (snd (f x)) + fst (snd (g y))))
    Iso.fun j (inl x') = {!!} , {!!} , {!!}
    Iso.fun j (inr y') = {!!}
    Iso.inv j = {!!}
    Iso.rightInv j = {!!}
    Iso.leftInv j = {!!}


