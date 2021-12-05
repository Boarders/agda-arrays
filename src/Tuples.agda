module Tuples where

open import Data.Nat
open import Data.Vec
open import Data.Vec as Vec
open import Data.List
open import Data.List as List
open import Data.Empty
open import Relation.Binary.PropositionalEquality


variable
  t  : Set
  ts : List Set


data Tuple : (n : ℕ) →  Vec Set n →  Set where
  nil  : Tuple 0 []
  cons : ∀ {n ty ts} → (t : ty) → Tuple n ts → Tuple (suc n) (ty ∷ ts)




zipDoms : ∀ {n} → (ts : Vec Set n) → (us : Vec Set n) → Set
zipDoms [] [] = {!!}
zipDoms (t₁ ∷ ts) (u₁ ∷ us) = {!!}
-- [t1 : t2 : t3 .. ] [u1 : u2 : u3 ..]
-- f (t1 -> u1 -> a1) ...
--zipWithT : Tuple n ts → Tuple n ts' → 


unzipT : (n m : ℕ) → (ts : Vec Set n) → Vec (Tuple n ts) m → Tuple n (Vec.map (λ t → Vec t m) ts)
unzipT .zero .zero [] [] = nil
unzipT .(suc _) .zero (x ∷ ts) [] = cons [] (unzipT _ zero ts [])
unzipT zero .(suc _) [] (x ∷ t) = nil
unzipT (suc n) suc[n]@.(suc _) (t ∷ ts) (v ∷ vs) with unzipT (suc n) _ (t ∷ ts) vs
... | tl = {!!}

{-
When people first start to use coq or isabelle, you don't hear from them for two years. They sort of, go _dark_. And then they emerge, you know, with all their pain receptors destroyed.


-}
