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

open import CLAP-BASE (ᵢ+ 29)
open import CLAP-MONAD (ᵢ+ 29)


test1 : CM ⊤
test1 = do c₁ ← const-gate (ᵢ+ 3)
           c₂ ← const-gate (ᵢ+ 0)
           c₃ ← add-gate c₁ c₂
           c₄ ← mul-gate c₁ c₂
           assert-eq0 c₂
           assert-neq0 c₁
           add-gate c₁ c₁
           return tt


trace1 = runTrace test1
cs1    = runCS    test1



_ : satCS' (proj₂ cs1) trace1 ≡ true
_ = refl


test2 : CM Var
test2 = do c₁ ← const-gate (ᵢ+ 0)
           c₂ ← iszero-gate c₁
           return c₂

trace2 = runTrace test2
cs2    = runCS  test2

_ : satCS cs2 trace2 ≡ true
_ = refl


test3 : CM Var
test3 = do c₁ ← const-gate (ᵢ+ 1)
           cond ← iszero-gate c₁
           trueBranch ← const-gate (ᵢ+ 4)
           falseBranch ← const-gate (ᵢ+ 2)
           r ← if-then-else cond trueBranch falseBranch
           return r


trace3 = runTrace test3
cs3    = runCS test3

_ : satCS cs3 trace3 ≡ true
_ = refl


test4 : CM Var
test4 = do c ← const-gate (ᵢ+ 3)
           minus-one ← const-gate (-[1+ 0 ])
           c' ← mul-gate minus-one c
           c' ← add-gate c c'
           cond ← iszero-gate c'
           trueBranch ← const-gate (ᵢ+ 2)
           falseBranch ← const-gate (ᵢ+ 0)
           r    ← if-then-else cond trueBranch falseBranch
           return r


trace4 = runTrace test4
cs4    = runCS test4

_ : satCS cs4 trace4 ≡ true
_ = refl



test5 : CM (Var × Var)
test5 = do c  ← const-gate (ᵢ+ 1)
           v1 ← const-gate (ᵢ+ 2)
           v2 ← const-gate (ᵢ+ 3)
           swap-gate c v1 v2


trace5 = runTrace test5
cs5    = runCS test5



test6' : ℕ → Var → CM Var
test6' n v = iter n (return v) q
  where
   q : Var → CM Var
   q z = do r ← mul-gate z v
            return r

test6 : CM Var
test6 = do c ← const-gate (ᵢ+ 3)
           q ← test6' 2 c
           return c

trace6 = runTrace test6
cs6    = runCS test6


_ : satCS cs6 trace6 ≡ true
_ = refl


{- computes 1+2+3+...+n -}
test7 : ℕ → CM Var
test7 n = do count ← const-gate (ᵢ+ 0)
             acc ← const-gate (ᵢ+ 0)
             q  ← iter n (return (acc ,, count)) 
                                (λ (acc ,, count)  → do one ← const-gate (ᵢ+ 1)
                                                        count ← add-gate count one
                                                        acc  ← add-gate acc count
                                                        assert-neq0 acc
                                                        return (acc ,, count))
             return (proj₁ q)
      


trace7 = runTrace (test7 5)
cs7    = runCS (test7 5)

_ : satCS cs7 trace7 ≡ true
_ = refl


