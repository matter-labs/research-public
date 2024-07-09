
module Extra where
open import Data.List
open import Data.Nat
open import Data.Maybe
open import Data.Bool

lkp-gen : {A : Set} → A → ℕ → List A → A
lkp-gen d zero [] = d
lkp-gen d zero (x ∷ l) = x
lkp-gen d (suc x) [] = d
lkp-gen d (suc x) (x₁ ∷ l) = lkp-gen d x l


lkpmb : {A : Set} →  ℕ → List A → Maybe A
lkpmb zero [] = nothing
lkpmb zero (x ∷ l) = just x
lkpmb (suc x) [] = nothing
lkpmb (suc x) (x₁ ∷ l) = lkpmb x l


mb2b : Maybe Bool → Bool
mb2b (just x) = x
mb2b nothing = false

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; decSetoid)

and-lft : (a b : Bool) → a ∧ b ≡ true → a ≡ true
and-lft true true p = refl

and-rgt : (a b : Bool) → a ∧ b ≡ true → b ≡ true
and-rgt true true p = refl

and-int : (a b : Bool) → a ≡ true → b ≡ true → a ∧ b ≡ true
and-int true true p1 p2 = refl



mlength-++ : {A : Set} → (l1 l2 : List A) →  length (l1 ++ l2) ≡ length l1 + length l2
mlength-++ [] l2 = refl
mlength-++ (x ∷ l1) l2 = Eq.cong suc (mlength-++ l1 l2)

