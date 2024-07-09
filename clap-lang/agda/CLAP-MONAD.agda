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

open import CLAP-INSTANCE modulus
module CLAP-MONAD-ℤ =  CLAP-BASE-ℤ
open  CLAP-MONAD-ℤ

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

runTrace : {A : Set} → CM A → List ℤ
runTrace cm = let (n ,, v ,, c) = cm 0 in genTrace c []

runCS : {A : Set} → CM A → CS
runCS cm = let (n ,, v ,, c) = cm 0 in genCS c (0 ,, [])


add-gate : Var → Var → CM Var
add-gate v1 v2  = λ n → suc n ,, n ,, gate (add v1 v2)

const-gate : ℤ → CM Var
const-gate z = λ n → suc n ,, n ,, gate (const z)

assert-eq0 :  Input → CM ⊤
assert-eq0 v  = λ n → n ,, tt ,, gate (eq0 v)
