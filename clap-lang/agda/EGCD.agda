{-# OPTIONS --warning=noModuleDoesntExport #-}
open import Data.Integer renaming (_+_ to _+ᵢ_ ; _*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
  using (_≤ᵇ_ ; ℤ ; _+ᵢ_ ; _*ᵢ_ ; _≟z_ ; Sign ; ᵢ+_ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )
module EGCD (modulus : ℤ) where

open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; decSetoid)
open import Data.Unit hiding (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_ ; _≤?_; z≤n; s≤s; _+_; _*_ ; _≟_ ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)

open import Data.List renaming (map to mapₗ ; find to findₗ ; zip to zipₗ ; concat to concatₗ) hiding (fromMaybe)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.AllPairs


open import Data.List.Membership.DecPropositional {_} {ℕ}  _≟_
open import Data.List.Relation.Unary.Unique.DecPropositional {_} {ℕ} _≟_
open import Data.List.Properties
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.Bool hiding (_≤_ ; _≤?_) renaming (_≟_ to _≟b_)
open import Data.Maybe renaming (_>>=_ to _>>=m_)
open import Data.Sum hiding ([_,_])

open import Data.Nat.Properties using (≤-totalOrder)
open import Data.List.Extrema ≤-totalOrder

open import Relation.Nullary



_≡ᵇz_ : ℤ → ℤ → Bool
x ≡ᵇz y = isYes (x ≟z y)

_%%_ : ℤ → ℤ → ℤ
a %% b with b ≟z (ᵢ+ 0)
... | .true because ofʸ a₁ = (ᵢ+ 4)
... | .false because ofⁿ ¬a = ᵢ+ _%_ a b ⦃ ≢-nonZero ¬a  ⦄

_%/_ : ℤ → ℤ → ℤ
a %/ b with b ≟z (ᵢ+ 0)
... | .true because ofʸ a₁ = (ᵢ+ 4)
... | .false because ofⁿ ¬a = _/_ a b ⦃ ≢-nonZero ¬a  ⦄

signum : ℤ → ℤ
signum (ᵢ+_ zero) = ᵢ+ zero
signum (ᵢ+_ (suc n)) = ᵢ+ 1
signum (-[1+_] n) = -[1+ 0 ]

{-# TERMINATING #-}
egcd : ℤ → ℤ → (ℤ × ℤ × ℤ)
egcd a (ᵢ+_ 0) = ᵢ+ ∣ a ∣ ,, signum a ,, ᵢ+ 4
egcd a b = let (g ,, x ,, y) = egcd b (a %% b) in (g ,, y ,, x - ((a %/ b) *ᵢ y))

inverse : ℤ → ℤ → ℤ
inverse a m = let (x ,, z ,, y) = egcd m a in y %% m
