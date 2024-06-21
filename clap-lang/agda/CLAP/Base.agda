open import Level using (0ℓ)

open import Data.Nat
open import Data.Vec
open import Data.Maybe renaming (zipWith to zipWithMaybe)
open import Data.Bool

open import Relation.Nullary.Decidable

open import CLAP.Field

module CLAP.Base (F : Field {ℓ = 0ℓ}) where

open Field F using (_≈_; dec≈) renaming (Carrier to Val; _+_ to _+F_; _*_ to _*F_; 0# to 0F; 1# to 1F)

data Circuit : ℕ → ℕ → Set where
  
  const   : (v : Val) → Circuit 0 1
  add     : Circuit 2 1
  mul     : Circuit 2 1
  isZero  : Circuit 1 1
  eq0     : Circuit 1 0
  neq0    : Circuit 1 0

  empty   : Circuit 0 0
  id      : Circuit 1 1
  copy    : Circuit 1 2
  discard : Circuit 1 0
  swap    : Circuit 2 2  

  seq     : ∀ {m n p} → Circuit m n → Circuit n p → Circuit m p
  par     : ∀ {m n p q} → Circuit m n → Circuit p q → Circuit (m + p) (n + q)

ite≈0F : ∀ {A : Set} → Val → A → A → A
ite≈0F v tv fv =
  if (Dec.does (dec≈ v 0F))
    then tv
    else fv

⟦_⟧ : ∀ {m n} → Circuit m n → Vec Val m → Maybe (Vec Val n)
⟦ const v ⟧   []             = just [ v ]
⟦ add ⟧       (v₁ ∷ v₂ ∷ []) = just [ v₁ +F v₂ ]
⟦ mul ⟧       (v₁ ∷ v₂ ∷ []) = just [ v₁ *F v₂ ]
⟦ isZero ⟧    (v ∷ [])       = just [ ite≈0F v 1F 0F ]
⟦ eq0 ⟧       (v ∷ [])       = ite≈0F v (just []) nothing
⟦ neq0 ⟧      (v ∷ [])       = ite≈0F v nothing (just [])
⟦ empty ⟧     []             = just []
⟦ id ⟧        (v ∷ [])       = just [ v ]
⟦ copy ⟧      (v ∷ [])       = just (v ∷ v ∷ [])
⟦ discard ⟧   _              = just []
⟦ swap ⟧      (v₁ ∷ v₂ ∷ []) = just (v₂ ∷ v₁ ∷ [])
⟦ seq c₁ c₂ ⟧         inpt   = just inpt >>= ⟦ c₁ ⟧ >>= ⟦ c₂ ⟧
⟦ par {m = m} c₁ c₂ ⟧ inpt   = let
    inpt₁ = take m inpt
    inpt₂ = drop m inpt
  in zipWithMaybe _++_ (⟦ c₁ ⟧ inpt₁) (⟦ c₂ ⟧ inpt₂)


