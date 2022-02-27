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
--open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import lemma
open import g-card

module finSet where

naiveFinSet : (Σ[ A ∈ Type₀ ] (Σ[ n ∈ ℕ ] (A ≡ Fin n))) ≃ ℕ
naiveFinSet = isoToEquiv i
  where
  i : Iso (Σ[ A ∈ Type₀ ] (Σ[ n ∈ ℕ ] (A ≡ Fin n))) ℕ
  Iso.fun i (A , n , p) = n
  Iso.inv i n = Fin n , n , refl
  Iso.rightInv i n = refl
  Iso.leftInv i (A , n , p) = ΣPathP (sym p , toPathP (ΣPathP (refl , aux)))
    where
    aux =
      subst (λ A → A ≡ Fin n) (sym p) refl ≡⟨ subst≡ₗ (sym p) refl ⟩
      (sym (sym p)) ∙ refl ≡⟨ sym (rUnit (sym (sym p))) ⟩
      sym (sym p) ≡⟨ refl ⟩
      p ∎

isFinSet : Type₀ → Type₁
isFinSet A = Σ[ n ∈ ℕ ] ∥ A ≡ Fin n ∥

FinSet : Type₁
FinSet = Σ[ A ∈ Type₀ ] (isFinSet A)

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

finSuc : {n : ℕ} → Fin (suc n) ≃ Fin n ⊎ Unit
finSuc {n} = isoToEquiv i
  where
  i : Iso (Fin (suc n)) (Fin n ⊎ Unit)
  Iso.fun i (a , zero , p) = inr tt
  Iso.fun i (a , suc b , p) = inl (a , b , injSuc p)
  Iso.inv i (inl (a , b , p)) = a , (suc b) , (cong suc p)
  Iso.inv i (inr tt) = n , 0 , refl
  Iso.leftInv i (a , zero , p) = Σ≡Prop (λ m → m≤n-isProp) (injSuc (sym p))
  Iso.leftInv i (a , suc b , p) = Σ≡Prop (λ m → m≤n-isProp) refl
  Iso.rightInv i (inl (a , b , p)) = cong inl (Σ≡Prop (λ m → m≤n-isProp) refl)
  Iso.rightInv i (inr tt) = refl

equivFinSuc : (n m : ℕ) → Fin (suc n) ≃ Fin (suc m) →  Fin n ≃ Fin m
equivFinSuc n m e = inj-⊎-Unit (compEquiv (invEquiv finSuc) (compEquiv e finSuc))

equivFinSucId : (n : ℕ) → equivFinSuc n n (idEquiv (Fin (suc n))) ≡ idEquiv (Fin n)
equivFinSucId n = 
  inj-⊎-Unit (compEquiv (invEquiv finSuc) (compEquiv (idEquiv (Fin (suc n))) finSuc)) ≡⟨ cong (λ f →  inj-⊎-Unit (compEquiv (invEquiv finSuc) f)) (compEquivIdEquiv finSuc) ⟩
  inj-⊎-Unit (compEquiv (invEquiv finSuc) finSuc) ≡⟨ cong (λ f → inj-⊎-Unit f) (invEquiv-is-linv finSuc) ⟩
  inj-⊎-Unit (idEquiv ((Fin n) ⊎ Unit)) ≡⟨ inj-⊎-Unit-Id ⟩
  idEquiv (Fin n) ∎

--compEquivFinSuc : (n m o : ℕ) → (e : Fin (suc n) ≃ Fin (suc m)) → (f : Fin (suc m) ≃ Fin (suc o)) → equivFinSuc n o (compEquiv e f) ≡ compEquiv (equivFinSuc n m e) (equivFinSuc m o f)
--compEquivFinSuc n m o e f = 
--  inj-⊎-Unit (compEquiv (invEquiv finSuc) (compEquiv (compEquiv e f) finSuc)) ≡⟨ {!!} ⟩
--  compEquiv (inj-⊎-Unit (compEquiv (invEquiv finSuc) (compEquiv e finSuc))) (inj-⊎-Unit (compEquiv (invEquiv finSuc) (compEquiv f finSuc))) ∎


F0notFs : (n : ℕ) → Fin (suc n) ≃ Fin 0 → ⊥
F0notFs n e = ¬Fin0 (equivFun e fzero)

injFin : (n m : ℕ) → Fin n ≃ Fin m → n ≡ m
injFin zero zero e = refl
injFin zero (suc m) e = ⊥-rec (F0notFs m (invEquiv e))
injFin (suc n) zero e = ⊥-rec (F0notFs n e)
injFin (suc n) (suc m) e = cong suc (injFin n m (equivFinSuc n m e))

∥injFin∥ : {n m : ℕ} → ∥ Fin n ≃ Fin m ∥ → n ≡ m
∥injFin∥ {n} {m} = trunc-rec (isSetℕ n m) (injFin n m)

injFinId : (n : ℕ) → injFin n n (idEquiv (Fin n)) ≡ refl
injFinId zero = refl
injFinId (suc n) = 
  injFin (suc n) (suc n) (idEquiv (Fin (suc n))) ≡⟨ refl ⟩
  cong suc (injFin n n (equivFinSuc n n (idEquiv (Fin (suc n))))) ≡⟨ cong (λ f → cong suc (injFin n n f)) (equivFinSucId n) ⟩
  cong suc (injFin n n (idEquiv (Fin n))) ≡⟨ cong (λ p → cong suc p) (injFinId n) ⟩
  cong suc refl ≡⟨ refl ⟩
  refl ∎

--compInjFin : (n m o : ℕ) (e : Fin n ≃ Fin m) → (f : Fin m ≃ Fin o) → injFin n o (compEquiv e f) ≡ (injFin n m e) ∙ (injFin m o f)
--compInjFin zero zero zero e f = refl
--compInjFin zero zero (suc o) e f =  ⊥-rec (F0notFs o (invEquiv f))
--compInjFin zero (suc m) o e f =  ⊥-rec (F0notFs m (invEquiv e))
--compInjFin (suc n) zero o e f =  ⊥-rec (F0notFs n e)
--compInjFin (suc n) (suc m) zero e f = ⊥-rec (F0notFs m f)
--compInjFin (suc n) (suc m) (suc o) e f = 
 -- cong suc (injFin n o (equivFinSuc n o (compEquiv e f))) ≡⟨ {!!} ⟩
 -- cong suc (injFin n o (compEquiv (equivFinSuc n m e) (equivFinSuc m o f))) ≡⟨ cong (λ e → cong suc e) (compInjFin n m o (equivFinSuc n m e) (equivFinSuc m o f)) ⟩
  --cong suc ((injFin n m (equivFinSuc n m e)) ∙ (injFin m o (equivFinSuc m o f))) ≡⟨ refl ⟩
  --(cong suc (injFin n m (equivFinSuc n m e))) ∙ (cong suc (injFin m o (equivFinSuc m o f))) ∎
    
claim-2-2 : {A B : FinSet} → ∥ fst A ≃ fst B ∥ → card A ≡ card B
claim-2-2 {A , n , q} {B , m , q'} equiv = ∥injFin∥ (∥compEquiv∥ (∥compEquiv∥ ((trunc-rec isPropPropTrunc (λ p → ∣ pathToEquiv (sym p) ∣) q)) equiv) (trunc-rec isPropPropTrunc (λ p → ∣ pathToEquiv p ∣) q'))

⊥≃Fin0 : ⊥ ≃ Fin 0
⊥≃Fin0 = isoToEquiv i
  where
  i : Iso ⊥ (Fin 0)
  Iso.fun i ()
  Iso.inv i x = ¬Fin0 x
  Iso.leftInv i ()
  Iso.rightInv i x = ⊥-rec (Iso.inv i x)

+-Fin : {n m : ℕ} → Fin (n + m) ≃ Fin n ⊎ Fin m
+-Fin {0} {m} = 
  Fin m ≃⟨ invEquiv ⊎-⊥-≃ ⟩
  Fin m ⊎ ⊥ ≃⟨ ⊎-swap-≃ ⟩
  ⊥ ⊎ Fin m ≃⟨ ⊎Equiv ⊥≃Fin0 (idEquiv (Fin m)) ⟩
  Fin 0 ⊎ Fin m ■

+-Fin {suc n} {m} = 
  Fin (suc n + m) ≃⟨ finSuc ⟩
  Fin (n + m) ⊎ Unit ≃⟨ ⊎Equiv +-Fin (idEquiv Unit) ⟩
  (Fin n ⊎ Fin m) ⊎ Unit ≃⟨ ⊎-assoc-≃ ⟩
  Fin n ⊎ (Fin m ⊎ Unit) ≃⟨ ⊎-swap-≃ ⟩
  (Fin m ⊎ Unit) ⊎ Fin n ≃⟨ ⊎Equiv ⊎-swap-≃ (idEquiv (Fin n)) ⟩
  (Unit ⊎ Fin m) ⊎ Fin n ≃⟨ ⊎-swap-≃ ⟩
  Fin n ⊎ (Unit ⊎ Fin m) ≃⟨ invEquiv ⊎-assoc-≃ ⟩
  (Fin n ⊎ Unit) ⊎ Fin m ≃⟨ ⊎Equiv (invEquiv finSuc) (idEquiv (Fin m)) ⟩
  Fin (suc n) ⊎ Fin m ■

_+ₙ_ : FinSet → FinSet → FinSet
(A , n , p) +ₙ (B , m , q) = (A ⊎ B) , n + m , ∥ua∥ (∥compEquiv∥ (∥⊎Equiv∥ (∥pathToEquiv∥ p) (∥pathToEquiv∥ q)) ∣ invEquiv +-Fin ∣)

claim-2-3 : {A B : FinSet} → card (A +ₙ B) ≡ card A + card B
claim-2-3 = refl

·-Fin : {n m : ℕ} → Fin (n · m) ≃ Fin n × Fin m
·-Fin {zero} {m} = 
  Fin 0 ≃⟨ invEquiv ⊥≃Fin0 ⟩
  ⊥ ≃⟨ invEquiv ×-⊥-≃ ⟩
  Fin m × ⊥ ≃⟨ ×-≃ (idEquiv (Fin m)) ⊥≃Fin0 ⟩
  Fin m × Fin 0 ≃⟨ swapEquiv (Fin m) (Fin 0) ⟩
  Fin 0 × Fin m ■

·-Fin {suc n} {m} = 
  Fin ((suc n) · m) ≃⟨ +-Fin ⟩
  Fin m ⊎ Fin (n · m) ≃⟨ ⊎Equiv (idEquiv (Fin m)) ·-Fin ⟩
  Fin m ⊎ (Fin n × Fin m) ≃⟨ ⊎Equiv (invEquiv ×-Unit-≃) (idEquiv (Fin n × Fin m)) ⟩
  (Fin m × Unit) ⊎ (Fin n × Fin m) ≃⟨ ⊎Equiv (swapEquiv (Fin m) Unit) (idEquiv (Fin n × Fin m)) ⟩
  (Unit × Fin m) ⊎ (Fin n × Fin m) ≃⟨ invEquiv ⊎-×-distrib ⟩
  (Unit ⊎ Fin n) × Fin m ≃⟨ ×-≃ ⊎-swap-≃ (idEquiv (Fin m)) ⟩
  (Fin n ⊎ Unit) × Fin m ≃⟨ ×-≃ (invEquiv finSuc) (idEquiv (Fin m)) ⟩
  Fin (suc n) × Fin m ■

_×ₙ_ : FinSet → FinSet → FinSet
(A , n , p) ×ₙ (B , m , q) = (A × B) , n · m ,  ∥ua∥ (∥compEquiv∥ (∥×-≃∥ (∥pathToEquiv∥ p) (∥pathToEquiv∥ q)) ∣ invEquiv ·-Fin ∣)

claim-2-6 : {A B : FinSet} → card (A ×ₙ B) ≡ card A · card B
claim-2-6 = refl


fiber-card : (n : ℕ) → (fiber card n) ≡ (Σ[ A ∈ Type₀ ] ∥ A ≡ Fin n ∥)
fiber-card n = 
  fiber card n ≡⟨ refl ⟩
  (Σ[ (A , m , ∣p∣) ∈ FinSet ] (m ≡ n))                                      ≡⟨ sym (ua (Ex-2-10 Type₀ isFinSet λ {(A , m , ∣p∣) → m ≡ n})) ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ (m , ∣p∣) ∈ isFinSet A ] (m ≡ n)))                     ≡⟨ Σ-cong-snd (λ A → sym (ua (Ex-2-10 ℕ (λ m → ∥ A ≡ Fin m ∥) λ {(m , ∣p∣) → m ≡ n}))) ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ m ∈ ℕ ] (Σ[ ∣p∣ ∈ ∥ A ≡ Fin m ∥ ] (m ≡ n))))           ≡⟨ refl ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ m ∈ ℕ ] (∥ A ≡ Fin m ∥ ×Σ (m ≡ n))))                  ≡⟨  Σ-cong-snd (λ A → Σ-cong-snd (λ m → ua e)) ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ m ∈ ℕ ] (∥ A ≡ Fin n ∥ ×Σ (m ≡ n))))                  ≡⟨ refl ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ m ∈ ℕ ] (Σ[ ∣p∣ ∈ ∥ A ≡ Fin n ∥ ] (m ≡ n))))           ≡⟨ Σ-cong-snd (λ A → Σ-cong-snd (λ m → Σ-cong-snd λ ∣p∣ → ua (equivSym m n))) ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ m ∈ ℕ ] (Σ[ ∣p∣ ∈ ∥ A ≡ Fin n ∥ ] (n ≡ m))))           ≡⟨ Σ-cong-snd (λ A → ua Σ-comm) ⟩
  (Σ[ A ∈ Type₀ ] (Σ[ ∣p∣ ∈ ∥ A ≡ Fin n ∥ ] (Σ[ m ∈ ℕ ] (n ≡ m))))           ≡⟨ Σ-cong-snd (λ A → ua (lem-3-11-9-i λ _ → isContrSingl n)) ⟩
  (Σ[ A ∈ Type₀ ] (∥ A ≡ Fin n ∥))                                           ∎

    where

    aux : {A : Type₀} → {m n : ℕ} → m ≡ n → ∥ A ≡ Fin m ∥ → ∥ A ≡ Fin n ∥ ×Σ (m ≡ n)
    aux {m = m} {n = n} p = trunc-rec (×Prop isPropPropTrunc (isSetℕ m n)) λ q → ∣ q ∙ cong Fin p ∣ , p
    
    aux' : {A : Type₀} → {m n : ℕ} → m ≡ n → ∥ A ≡ Fin n ∥ → ∥ A ≡ Fin m ∥ ×Σ (m ≡ n)
    aux' {m = m} {n = n} p = trunc-rec (×Prop isPropPropTrunc (isSetℕ m n)) λ q → ∣ q ∙ cong Fin (sym p) ∣ , p

    e : {A : Type₀} → {m n : ℕ} → ∥ A ≡ Fin m ∥ ×Σ (m ≡ n) ≃ ∥ A ≡ Fin n ∥ ×Σ (m ≡ n)
    e {A = A} {m = m} {n = n} = ≃Prop (∥ A ≡ Fin m ∥ ×Σ (m ≡ n)) (∥ A ≡ Fin n ∥ ×Σ (m ≡ n)) (×Prop isPropPropTrunc (isSetℕ m n)) (×Prop isPropPropTrunc (isSetℕ m n)) (λ { (∣q∣ , p) → aux p ∣q∣} ) λ { (∣q∣ , p) → aux' p ∣q∣}

g-card-Fin : (n : ℕ) → (g-card (Fin n)) ≡ n
g-card-Fin zero = 
  g-card (Fin 0) ≡⟨ g-card-equiv ∣ invEquiv ⊥≃Fin0 ∣ ⟩
  g-card ⊥ ≡⟨ g-card-⊥ ⟩
  0 ∎
g-card-Fin (suc n) = 
  g-card (Fin (suc n)) ≡⟨ g-card-equiv ∣ finSuc ∣ ⟩
  g-card (Fin n ⊎ Unit) ≡⟨ g-card-⊎ ⟩
  (g-card (Fin n)) + (g-card Unit) ≡⟨ cong (λ m → m + (g-card Unit)) (g-card-Fin n) ⟩
  n + (g-card Unit) ≡⟨ cong (λ m → n + m) g-card-Unit ⟩
  n + 1 ≡⟨ +-comm n 1 ⟩
  suc n ∎

g-card-isFinSet : (A : Type₀) → (p : isFinSet A) → (g-card A) ≡ (card (A , p))
g-card-isFinSet A (n , ∣p∣) = 
  g-card A ≡⟨ g-card-equiv (∥pathToEquiv∥ ∣p∣) ⟩
  g-card (Fin n) ≡⟨ g-card-Fin n ⟩
  n ∎
  
≡Dec-ℕ : (m n : ℕ) → (Dec (m ≡ n))
≡Dec-ℕ zero zero = yes refl
≡Dec-ℕ zero (suc n) = no znots
≡Dec-ℕ (suc m) zero = no snotz
≡Dec-ℕ (suc m) (suc n) with (≡Dec-ℕ m n)
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (injSuc q))

≡Dec-Fin : {n : ℕ} → (x y : Fin n) → (Dec (x ≡ y))
≡Dec-Fin {n = n} (a ,  b , p) (a' , b' , q) with (≡Dec-ℕ a a') | (≡Dec-ℕ b b')
... | yes p' | yes q' = yes (ΣPathP (p' , ΣPathP (q' , toPathP aux)))
  where
  aux =
    transport (λ i → q' i + suc (p' i) ≡ n) p ≡⟨ refl ⟩
    subst2 (λ a b → a + suc b ≡ n) q' p' p ≡⟨ isSetℕ (b' + suc a') n (subst2 (λ a b → a + suc b ≡ n) q' p' p) q ⟩
    q ∎

... | _ | no ¬q' = no (λ P → ¬q' (λ i → fst (snd (P i))))
... | no ¬p' | _ = no (λ P → ¬p' (λ i → fst (P i)))


g-card-Aut-Fin : (n : ℕ) → (g-card (Aut (Fin n))) ≡ n !
g-card-Aut-Fin zero = 
  g-card (Aut (Fin 0)) ≡⟨ g-card-equiv ∣ pathToEquiv (cong Aut (ua (invEquiv ⊥≃Fin0))) ∣ ⟩
  g-card (Aut ⊥) ≡⟨ g-card-Aut-⊥ ⟩
  1 ∎

g-card-Aut-Fin (suc n) = {!!}
