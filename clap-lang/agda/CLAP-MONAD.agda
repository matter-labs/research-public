{-# OPTIONS --warning=noModuleDoesntExport #-}

open import Data.Integer renaming (_+_ to _+ᵢ_ ; _*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
  using (_≤ᵇ_ ; ℤ ; _+ᵢ_ ; _*ᵢ_ ; _≟z_ ; Sign ; ᵢ+_ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )

module CLAP-MONAD (modulus : ℤ)  where

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

open import CLAP-BASE modulus


Var = ℕ

CM : Set → Set
CM a = ℕ → ℕ × a × Circuit

_>>=_ : {A B : Set} → CM A → (A → CM B) → CM B
cma >>= cmb = λ n → let (next ,, a ,, c) = cma n in
                    let (next' ,, b ,, c')  =  cmb a next in
                    next' ,, b ,, seq c c'


return : {A : Set} → A → CM A
return a = λ n → n ,, a ,, empty


_>>_ : {A B : Set} → CM A → CM B → CM B
cma >> cmb = do a ← cma
                cmb


iter : {A : Set} → ℕ → CM A → (A → CM A) → CM A
iter zero cm₁ cm₂ = cm₁
iter (suc n) cm₁ cm₂ = iter n (cm₁ >>= (λ a → cm₂ a) ) cm₂


iter2 : {A : Set} → ℕ → CM (A × A)  → (A × A → CM (A × A)) → CM (A × A)
iter2 zero cm₁ cm₂ = cm₁
iter2 (suc n) cm₁ cm₂ = iter n ((cm₁ >>= (λ a → cm₂ a) )) cm₂


runTrace : {A : Set} → CM A → List ℤ
runTrace cm = let (n ,, v ,, c) = cm 0 in genTrace c []

runCS : {A : Set} → CM A → CS
runCS cm = let (n ,, v ,, c) = cm 0 in genCS c (0 ,, [])


add-gate : Var → Var → CM Var
add-gate v1 v2  = λ n → suc n ,, n ,, add v1 v2

mul-gate : Var → Var → CM Var
mul-gate v1 v2  = λ n → suc n ,, n ,, mul v1 v2

const-gate : ℤ → CM Var
const-gate z = λ n → suc n ,, n ,, const z

assert-eq0 :  Input → CM ⊤
assert-eq0 v  = λ n → n ,, tt ,, eq0 v

assert-neq0 :  Input → CM ⊤
assert-neq0 v  = λ n → 4 + n ,, tt ,, neq0 v


isZero-gate :  Input → CM Var
isZero-gate v  = λ n → 4 + n ,, 3 + n ,, isZero v


assert-bool : Input → CM ⊤
assert-bool i = do minus-one ← const-gate (-[1+ 0 ])
                   one ← const-gate (ᵢ+ 1)
                   m ← mul-gate minus-one i
                   r ← add-gate one m
                   r ← mul-gate i r
                   assert-eq0 r


iszero-gate : Var → CM Var
iszero-gate v = do c   ← isZero-gate v
                   minus-one ← const-gate (-[1+ 0 ])
                   q ← mul-gate c minus-one
                   return q

swap-gate : Var → Var → Var → CM (Var × Var)
swap-gate c v1 v2 = do minus-one ← const-gate (-[1+ 0 ])
                       one ← const-gate (ᵢ+ 1)
                       q ← mul-gate c minus-one
                       q ← add-gate one q
                       r11 ← mul-gate q v1
                       r12 ← mul-gate c v2
                       r21 ← mul-gate c v1
                       r22 ← mul-gate q v2
                       r1 ← add-gate r11 r12
                       r2 ← add-gate r21 r22
                       return (r1 ,, r2)



if-then-else : Var → Var → Var → CM Var
if-then-else v1 v2 v3 = do tb ← mul-gate v1 v2
                           minus-one ← const-gate (-[1+ 0 ])
                           one ← const-gate (ᵢ+ 1)
                           -cond  ← mul-gate v1 minus-one
                           1-cond ← add-gate one -cond
                           fb     ← mul-gate v3 1-cond
                           r      ← add-gate fb tb
                           return r
