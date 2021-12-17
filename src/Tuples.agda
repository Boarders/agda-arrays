module Tuples where

open import Data.Nat
open import Data.Vec
open import Data.Vec as Vec
open import Data.List
open import Data.List as List
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Vec.Recursive.Categorical
open import Category.Applicative
open RawApplicative using (pure)
open import Level using (Level)

variable
  aℓ bℓ : Level
  A : Set aℓ
  B : Set bℓ
  a t  : Set
  n : ℕ
  ts ts' rs  : Vec Set n

data Tuple : (n : ℕ) →  Vec Set n →  Set where
  nil  : Tuple 0 []
  cons : ∀ {n ty ts} → (t : ty) → Tuple n ts → Tuple (suc n) (ty ∷ ts)

_⟨$⟩_ :  ∀ {n} → (A → B) → Vec A n → Vec B n
_⟨$⟩_ = Vec.map

fill : ∀ {n : ℕ} → a → Vec a n
fill = Vec.replicate

zipDoms : (ts : Vec Set n) → (us : Vec Set n) → (rs : Vec Set n) → Vec Set n
zipDoms ts us rs = (λ t u r → (t → u → r)) ⟨$⟩ ts ⊛ us ⊛ rs


zipWithT  :
  Tuple n ts  → Tuple n ts' → (rs : Vec Set n) → (Tuple n (zipDoms ts ts' rs)) → Tuple n rs
zipWithT nil nil [] nil = nil
zipWithT (cons t₁ ts) (cons t₂ ts') (res ∷ rs) (cons f₁ fs) =
  cons (f₁ t₁ t₂) (zipWithT ts ts' rs fs)

mkCons : {m : ℕ} → (n : ℕ) → (ts : Vec Set n) → Tuple _ (zipDoms ts (Vec.map (λ t -> Vec t m) ts) (Vec.map (λ t → Vec t (suc m)) ts))
mkCons zero [] = nil
mkCons (suc n) (t ∷ ts) = cons _∷_ (mkCons n ts)

unzipT : (n m : ℕ) → (ts : Vec Set n) → Vec (Tuple n ts) m → Tuple n (Vec.map (λ t → Vec t m) ts)
unzipT .zero .zero [] [] = nil
unzipT .(suc _) .zero (t ∷ ts) [] = cons [] (unzipT _ zero ts [])
unzipT zero .(suc _) [] (t ∷ ts) = nil
unzipT (suc n) suc[m]@.(suc _) ts@(t ∷ tl) (v ∷ vs) with unzipT (suc n) _ ts vs
... | rec = zipWithT v rec (Vec.map (λ t → Vec t suc[m]) ts) (mkCons (suc n) ts)

zipT : (n m : ℕ) → (ts : Vec Set n) → (Tuple n (Vec.map (λ t → Vec t m) ts)) → Vec (Tuple n ts) m
zipT zero m [] tps = fill tps
zipT (suc n) zero ts@(tp ∷ tps) (cons v1 vs) = []
zipT (suc n) suc[m]@(suc m) ts@(tp ∷ tps) (cons v1 vs) with zipT n (suc[m]) tps vs 
... | rec = {!!} ∷ {!!}

{-
"When people first start to use coq or isabelle, you don't hear from them for two years.
They sort of, go _dark_. And then they emerge, you know, with all their pain receptors destroyed." - SPJ
-}
