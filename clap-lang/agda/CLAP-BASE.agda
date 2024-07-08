{-# OPTIONS --warning=noModuleDoesntExport #-}

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_ ; _≤?_; z≤n; s≤s; _+_; _*_ ; _≟_ ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.List renaming (map to mapₗ ; find to findₗ ; zip to zipₗ ; concat to concatₗ) hiding (fromMaybe)
open import Data.Bool hiding (_≤_ ; _≤?_) renaming (_≟_ to _≟b_)

module CLAP-BASE (Field : Set) (zeroF :  Field)  (Gate : Set)(Expr : Set)
  (extInps-gate   : Gate → ℕ × List ℕ → ℕ × List ℕ)
  (WellFormedGate : Gate → ℕ × List ℕ → Set)
  (genTraceGate   : Gate → List Field → List Field)
  (genTraceAGate  : Gate → Bool × List Field → Bool × List Field)
  (genCS-gate     : Gate → ℕ × List Expr → ℕ × List Expr)
  (WFCS-expr      : Expr → ℕ → Set)
  (satCS'-expr    : Expr → List Field → Bool)
 where

open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; decSetoid)
open import Data.Unit hiding (_≟_)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.AllPairs

open import Data.List.Membership.DecPropositional {_} {ℕ}  _≟_
open import Data.List.Relation.Unary.Unique.DecPropositional {_} {ℕ} _≟_
open import Data.List.Properties
open import Data.Product renaming (_,_ to _,,_) hiding (map)

open import Data.Maybe renaming (_>>=_ to _>>=m_)
open import Data.Sum hiding ([_,_])

open import Data.Nat.Properties using (≤-totalOrder)
open import Data.List.Extrema ≤-totalOrder

open import Relation.Nullary


CS = ℕ × List Expr

Input = ℕ

data Circuit : Set where
  empty  : Circuit
  seq    : Circuit → Circuit → Circuit
  par    : Circuit → Circuit → Circuit  
  gate   : Gate → Circuit


extInps : Circuit → ℕ × List ℕ → ℕ × List ℕ
extInps empty (n ,, l) = n ,, l
extInps (seq c c₁) (n ,, l) = extInps c₁ (extInps c (n ,, l))
extInps (par c c₁) (n ,, l) = extInps c₁ (extInps c (n ,, l))
extInps (gate g) poses = extInps-gate g poses

WellFormedCircuit : Circuit → ℕ × List ℕ → Set
WellFormedCircuit empty l = ⊤
WellFormedCircuit (seq c₁ c₂) (n ,, l) = WellFormedCircuit c₁ (n ,, l) × WellFormedCircuit c₂ (extInps c₁ (n ,, l))
WellFormedCircuit (par c₁ c₂) (n ,, l) = WellFormedCircuit c₁ (n ,, l) × WellFormedCircuit c₂ (n ,, l) × WellFormedCircuit c₂ (extInps c₁ (n ,, l))
WellFormedCircuit (gate g) = WellFormedGate g

WFCS : List Expr → ℕ → Set
WFCS [] n = ⊤
WFCS (x ∷ xs) n = WFCS-expr x n × WFCS xs n

lkp : ℕ → List Field → Field
lkp zero [] = zeroF
lkp zero (x ∷ l) = x
lkp (suc x) [] = zeroF
lkp (suc x) (x₁ ∷ l) = lkp x l

genTrace : Circuit → List Field → List Field
genTrace empty t = t
genTrace (seq c c₁) t = genTrace c₁ (genTrace c t)
genTrace (par c c₁) t = genTrace c₁ (genTrace c t)
genTrace (gate g) t = genTraceGate g t


genCS : Circuit → CS → CS
genCS (gate x) cs = genCS-gate x cs
genCS (seq c c₁) cs = genCS c₁ (genCS c cs)
genCS (par c c₁) cs = genCS c₁ (genCS c cs)
genCS empty cs = cs

lkpmb : ℕ → List Field → Maybe Field
lkpmb zero [] = nothing
lkpmb zero (x ∷ l) = just x
lkpmb (suc x) [] = nothing
lkpmb (suc x) (x₁ ∷ l) = lkpmb x l


mb2b : Maybe Bool → Bool
mb2b (just x) = x
mb2b nothing = false


genTraceA : Circuit → Bool × List Field → Bool × List Field
genTraceA empty (b ,, t) = b ,, t
genTraceA (seq c c₁) bt = genTraceA c₁ (genTraceA c bt)
genTraceA (par c c₁) bt = genTraceA c₁ (genTraceA c bt)
genTraceA (gate x) bt = genTraceAGate x bt 

satCS' : List Expr → List Field → Bool
satCS' [] trace = true
satCS' (x ∷ xs) trace = satCS'-expr x trace

satCS : CS → List Field → Bool
satCS (fst ,, snd) t = (length t ≡ᵇ fst) ∧ satCS' snd t

projPos : List ℕ → List Field → List Field
projPos [] l = []
projPos (x ∷ n) l = lkp x l ∷ projPos n l

PosCorrect : ℕ × List ℕ → Set
PosCorrect pos = (x : ℕ) → x ∈ proj₂ pos → suc x ≤ proj₁ pos
