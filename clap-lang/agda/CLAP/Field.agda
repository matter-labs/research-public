open import Data.Product
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_)
import Algebra.Structures as AStr

module CLAP.Field
  {a ℓ} 
  where

open import Level using (suc; _⊔_)
open import Algebra.Core

module _
  {A : Set a}
  (_≈_ : Rel A ℓ)
  where

  open AStr _≈_
  
  record IsField
           (_+_ _·_ : Op₂ A) (-_ : Op₁ A) (0r 1r : A) : Set (a ⊔ ℓ) where
    field
      isCommutativeRing : IsCommutativeRing _+_ _·_ -_ 0r 1r
      hasInverse : (x : A) → ¬ x ≈ 0r → Σ[ y ∈ A ] ((x · y) ≈ 1r)
      0≢1        : ¬ 0r ≈ 1r

record Field : Set (suc (a ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier           : Set a
    _≈_               : Rel Carrier ℓ
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    -_                : Op₁ Carrier
    0#                : Carrier
    1#                : Carrier
    isField : IsField _≈_ _+_ _*_ -_ 0# 1#
    dec≈ : Decidable _≈_

  open IsField isField public


