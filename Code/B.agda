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
    β β' β''  : Level
    A B C D : Type β

data πΉ : Typeβ where
  obj : β β πΉ
  hom : {m n : β} β Fin m β‘ Fin n β obj m β‘ obj n
  hom-id : {n : β} β hom (refl {x = Fin n}) β‘ refl
  hom-comp : {m n o : β} (p : Fin m β‘ Fin n) (q : Fin n β‘ Fin o) β hom (p β q) β‘ hom p β hom q

--πΉtoβ : πΉ βΒ β
--πΉtoβ (obj n) = n
--πΉtoβ (hom {m = m} {n = n} p i) = (injFin m n (pathToEquiv p)) i
--πΉtoβ (hom-idΒ {n = n} i j) = aux i j
--  where
--  aux =
--    injFin  n n (pathToEquiv refl) β‘β¨ cong (Ξ» f β injFin n n f) pathToEquivRefl β©
--    injFin n n (idEquiv (Fin n)) β‘β¨ injFinId n β©
--    refl β
--πΉtoβ (hom-comp {m = m} {n = n} {o = o} p q i j) = aux i j
--  where
--  aux = 
--    injFin m o (pathToEquiv (p β q)) β‘β¨ cong (Ξ» p β injFin m o p) (sym (compEquivPathToEquiv p q)) β©
--    injFin m o (compEquiv (pathToEquiv p) (pathToEquiv q)) β‘β¨ {!!} β©
--    (injFin m n (pathToEquiv p)) β (injFin n o (pathToEquiv q)) β

--πΉ-rec : isGroupoid A β (f : β β A) β (F : {m n : β} β Fin m β‘ Fin n β f m β‘ f n) β ({n : β} β F (refl {x = Fin n}) β‘ refl) β ({m n o : β} β (p : Fin m β‘ Fin n) β (q : Fin n β‘ Fin o) β F (p β q) β‘ (F p) β (F q)) β (πΉ β A)
--πΉ-rec grp f F idF compF (obj n) = f n
--πΉ-rec grp f F idF compF (hom p i) = F p i
--πΉ-rec grp f F idF compF (hom-id {n = n} i j) = idF {n = n} i j
--πΉ-rec grp f F idF compF (hom-comp {m = m} {n = n} {o = o} p q i j) = {!!}

postulate
  πΉtoβ : πΉ βΒ β
  πΉtoβ-obj : (n : β) β πΉtoβ (obj n) β‘ n
