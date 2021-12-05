module Prim where

open import Data.Nat
open import Categories.Category.Core
open import Level
open import Relation.Binary.PropositionalEquality
open import Function

⊔
postulate
  Word8  : Set
  Int    : Set
  Double : Set

data PrimU : Set where
  Word8U  : PrimU
  IntU    : PrimU
  DoubleU : PrimU

⟦_⟧ : PrimU → Set
⟦ Word8U ⟧ = Word8
⟦ IntU ⟧ = Int
⟦ DoubleU ⟧ = Double

PrimMor : PrimU → PrimU → Set
PrimMor p q = ⟦ p ⟧  → ⟦ q ⟧

Prim∘ : {A B C : PrimU} → (⟦ B ⟧ → ⟦ C ⟧) → (⟦ A ⟧ → ⟦ B ⟧) → ⟦ A ⟧ → ⟦ C ⟧
Prim∘ f g = f ∘ g

primCat : Category 0ℓ 0ℓ 0ℓ
primCat = record
            { Obj = PrimU
            ; _⇒_ = PrimMor
            ; _≈_ = _≡_
            ; id = λ ⟦p⟧ → ⟦p⟧
            ; _∘_ = Prim∘
            ; assoc = refl
            ; sym-assoc = refl
            ; identityˡ = refl
            ; identityʳ = refl
            ; identity² = refl
            ; equiv = {!!}
            ; ∘-resp-≈ = {!!}
            }

postulate
  PArray : ℕ → PrimU → Set
  
