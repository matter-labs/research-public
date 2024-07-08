{-# OPTIONS --warning=noModuleDoesntExport #-}

open import Data.Integer renaming (_+_ to _+ᵢ_ ; _*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
  using (_≤ᵇ_ ; ℤ ; _+ᵢ_ ; _*ᵢ_ ; _≟z_ ; Sign ; ᵢ+_ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )
module CLAP-BASE (modulus : ℤ) where

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

open import EGCD (modulus)


Input = ℕ

data Circuit : Set where
  empty  : Circuit
  const  : ℤ → Circuit
  add    : Input → Input → Circuit
  seq    : Circuit → Circuit → Circuit
  eq0    : Input → Circuit -- assert  = 0


extInps : Circuit → ℕ × List ℕ → ℕ × List ℕ
extInps empty (n ,, l) = n ,, l
extInps (const x) (n ,, l) = suc n ,, (n ∷ l)
extInps (add x x₁) (n ,, l) = suc n ,, (n ∷ l)
extInps (seq c c₁) (n ,, l) = extInps c₁ (extInps c (n ,, l))
extInps (eq0 _) poses = poses




data Expr : Set where
  _+_＝_ : ℕ → ℕ → ℕ → Expr
  _*_＝_ : ℕ → ℕ → ℕ → Expr
  _＝c_  : ℕ → ℤ → Expr

WellFormedCircuit : Circuit → ℕ × List ℕ → Set
WellFormedCircuit empty l = ⊤
WellFormedCircuit (const x) l = ⊤
WellFormedCircuit (add x₁ x₂) (n ,, l) = x₁ ∈ l × x₂ ∈ l × (suc x₁ ≤ n) × (suc x₂ ≤  n)
WellFormedCircuit (eq0 x) (n ,, l) = x ∈ l × (suc x ≤ n)
WellFormedCircuit (seq c₁ c₂) (n ,, l) = WellFormedCircuit c₁ (n ,, l) × WellFormedCircuit c₂ (extInps c₁ (n ,, l))


WFCS : List Expr → ℕ → Set
WFCS [] n = ⊤
WFCS ((x + x₁ ＝ x₂) ∷ snd) n = (suc x ≤ n) × (suc x₁ ≤ n) × (suc x₂ ≤ n)  × WFCS (snd) n
WFCS ((x * x₁ ＝ x₂) ∷ snd) n = (suc x ≤ n) × (suc x₁ ≤ n) × (suc x₂ ≤ n)  × WFCS (snd) n
WFCS ((x ＝c x₁) ∷ snd) n = (suc x ≤ n) ×  WFCS (snd) n


CS = ℕ × List Expr

lkp : ℕ → List ℤ → ℤ
lkp zero [] = ᵢ+ 0
lkp zero (x ∷ l) = x
lkp (suc x) [] = ᵢ+ 0
lkp (suc x) (x₁ ∷ l) = lkp x l


--genTraceA _ = {!!}


--{-# TERMINATING #-}
genTrace : Circuit → List ℤ → List ℤ
genTrace (const x) t = t ++ [ x %% modulus ]
genTrace (eq0 x) t = t
genTrace empty t = t
genTrace (add x x₁) t = t ++ [ (lkp x t +ᵢ lkp x₁ t) %% modulus ]
genTrace (seq c c₁) t = genTrace c₁ (genTrace c t)



--{-# TERMINATING #-}
genCS : Circuit → CS → CS
genCS (const x) (fst ,, snd) = suc fst ,, fst ＝c x ∷ snd
genCS (eq0 x) (fst ,, snd) = fst ,, x ＝c (ᵢ+ 0) ∷ snd
genCS (add x x₁) (fst ,, snd) = suc fst ,, x + x₁ ＝ fst ∷ snd
genCS (seq c c₁) cs = genCS c₁ (genCS c cs)
genCS empty cs = cs


lkpmb : ℕ → List ℤ → Maybe ℤ
lkpmb zero [] = nothing
lkpmb zero (x ∷ l) = just x
lkpmb (suc x) [] = nothing
lkpmb (suc x) (x₁ ∷ l) = lkpmb x l


mb2b : Maybe Bool → Bool
mb2b (just x) = x
mb2b nothing = false


genTraceA : Circuit → Bool × List ℤ → Bool × List ℤ
genTraceA empty (b ,, t) = b ,, t
genTraceA (const x) (b ,, t) = b ,, t ++ [ x  %% modulus ]
genTraceA (eq0 x) (b ,, t) = b ∧ mb2b ((lkpmb x t) >>=m λ xv → just (xv  ≡ᵇz ((ᵢ+ 0) %% modulus) ))  ,, t
genTraceA (add x x₁) (b ,, t) = b ,, t ++ [ (lkp x t +ᵢ lkp x₁ t) %% modulus ]
genTraceA (seq c c₁) bt = genTraceA c₁ (genTraceA c bt)

 



satCS' : List Expr → List ℤ → Bool
satCS' [] trace = true
satCS' ((x + x₁ ＝ x₂) ∷ snd) trace =
   mb2b (lkpmb x trace >>=m (λ xc → lkpmb x₁ trace >>=m λ yc → lkpmb x₂ trace >>=m λ zc
    → just (isYes ((xc +ᵢ yc) %% modulus ≟z zc))))
              ∧ satCS' snd trace
satCS' ((x * x₁ ＝ x₂) ∷ snd) trace =
   mb2b (lkpmb x trace >>=m (λ xc → lkpmb x₁ trace >>=m λ yc → lkpmb x₂ trace >>=m λ zc
     → just (isYes ((xc *ᵢ yc) %% modulus ≟z zc %% modulus))))
              ∧ satCS' snd trace
satCS' ((x ＝c x₁) ∷ snd) trace =
  mb2b (lkpmb x trace >>=m (λ xv → just (xv ≡ᵇz (x₁ %% modulus))))
          ∧ satCS' snd trace


satCS : CS → List ℤ → Bool
satCS (fst ,, snd) t = (length t ≡ᵇ fst) ∧ satCS' snd t
