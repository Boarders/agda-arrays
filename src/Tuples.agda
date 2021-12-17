module Tuples where

open import Data.Nat
open import Data.Vec
open import Data.Vec as Vec
open import Data.List
open import Data.List as List
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Unit


variable
  a t  : Set
  n    : ℕ
  ts ts' rs  : Vec Set n

data Tuple : (n : ℕ) →  Vec Set n →  Set where
  nil  : Tuple 0 []
  cons : ∀ {n ty ts} → (t : ty) → Tuple n ts → Tuple (suc n) (ty ∷ ts)

fill : ∀ {n : ℕ} → a → Vec a n
fill {n = zero} a = []
fill {n = suc n} a = a ∷ fill a

zipDoms : (ts : Vec Set n) → (us : Vec Set n) (rs : Vec Set n) → Vec Set n
zipDoms [] [] [] = []
zipDoms (t₁ ∷ ts) (u₁ ∷ us) (r₁ ∷ rs)  = (t₁ → u₁ → r₁) ∷ (zipDoms ts us rs)

zipWithT  :
  Tuple n ts  → Tuple n ts' → (rs : Vec Set n) → (Tuple n (zipDoms ts ts' rs)) → Tuple n rs
zipWithT nil nil [] nil = nil
zipWithT (cons t₁ ts) (cons t₂ ts') (res ∷ rs) (cons f₁ fs) =
  cons (f₁ t₁ t₂) (zipWithT ts ts' rs fs)


unzipT : (n m : ℕ) → (ts : Vec Set n) → Vec (Tuple n ts) m → Tuple n (Vec.map (λ t → Vec t m) ts)
unzipT .zero .zero [] [] = nil
unzipT .(suc _) .zero (x ∷ ts) [] = cons [] (unzipT _ zero ts [])
unzipT zero .(suc _) [] (x ∷ t) = nil
unzipT (suc n) suc[m]@.(suc _) ts@(t ∷ tl) (v ∷ vs) with unzipT (suc n) _ ts vs
... | rec = zipWithT v rec (Vec.map (λ t → Vec t suc[m]) ts) {!!} -- zipWithT {!!} {!!} {!!} {!!}

{-
"When people first start to use coq or isabelle, you don't hear from them for two years. They sort of, go _dark_. And then they emerge, you know, with all their pain receptors destroyed." - SPJ
-}
