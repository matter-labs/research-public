{-# OPTIONS --warning=noModuleDoesntExport #-}
module CLAP-EXAMPLES where

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
open import Data.Integer renaming (_+_ to _+ᵢ_ ; _*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
  using (_≤ᵇ_ ; ℤ ; _+ᵢ_ ; _*ᵢ_ ; _≟z_ ; Sign ; ᵢ+_ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )
open import Data.Nat.Properties using (≤-totalOrder)
open import Data.List.Extrema ≤-totalOrder

open import Relation.Nullary


open import CLAP-MONAD (ᵢ+ 29)
open CLAP-MONAD-ℤ

test1 : CM ⊤
test1 = do c₁ ← const-gate (ᵢ+ 3)
           c₂ ← const-gate (ᵢ+ 0)
           c₃ ← add-gate c₁ c₂
           c₄ ← add-gate c₁ c₂
           assert-eq0 c₂
           add-gate c₁ c₁
           return tt

trace1 = runTrace test1
cs1    = runCS    test1



_ : satCS' (proj₂ cs1) trace1 ≡ true
_ = refl


test2 : CM ⊤
test2 = do c₁ ← const-gate (ᵢ+ 5)
           assert-eq0 c₁
           

trace2 = runTrace test2
cs2    = runCS  test2

_ : satCS cs2 trace2 ≡ false
_ = refl
