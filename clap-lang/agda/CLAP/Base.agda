open import Level using (0ℓ)

open import Data.Nat
open import Data.Vec
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (zipWith to zipWithMaybe)
open import Data.Bool
open import Data.Fin using (Fin; #_; _↑ˡ_; _↑ʳ_)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Vec.Relation.Unary.All using () renaming (All to AllV)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)

open import Relation.Nullary.Decidable
open import Relation.Nullary.Reflects
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import CLAP.Field

module CLAP.Base (F : Field {ℓ = 0ℓ}) where

open Field F using (_≈_; dec≈; sym) renaming
  (Carrier to Val;
  _+_ to _+F_;
  _*_ to _*F_;
  0# to 0F;
  1# to 1F;
  setoid to F-setoid)

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

  seq     : ∀ {m n p} → (c₁ : Circuit m n) → (c₂ : Circuit n p) → Circuit m p
  par     : ∀ {m n p q} → (c₁ : Circuit m n) → (c₂ : Circuit p q) → Circuit (m + p) (n + q)

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

countWires : ∀ {m n} → Circuit m n → ℕ
countWires {.0} {.1} (const v) = 1
countWires {.2} {.1} add = 3
countWires {.2} {.1} mul = 3
countWires {.1} {.1} isZero = 2
countWires {.1} {.0} eq0 = 1
countWires {.1} {.0} neq0 = 1
countWires {.0} {.0} empty = 0
countWires {.1} {.1} id = 2
countWires {.1} {.2} copy = 3
countWires {.1} {.0} discard = 1
countWires {.2} {.2} swap = 4
countWires {m} {n = p} (seq {n = n} circ circ₁) = m + n + p
countWires (par circ₁ circ₂) = countWires circ₁ + countWires circ₂

data Constraint (n : ℕ) : Set where
  _+_＝_ : (l : Fin n) → (r : Fin n) → (o : Fin n) → Constraint n
  _*_＝_ : (l : Fin n) → (r : Fin n) → (o : Fin n) → Constraint n
  _＝ₖ_  : (l : Fin n) → (v : Val) → Constraint n
  _＝ᵥ_  : (l : Fin n) → (o : Fin n) → Constraint n

ConstraintSystem : ℕ → Set
ConstraintSystem n = List (Constraint n)

infix 9 _+_＝_
infix 9 _*_＝_
infix 9 _＝ₖ_ 
infix 9 _＝ᵥ_

Trace = Vec Val

satisfies : ∀ {n} → Trace n → Constraint n → Set
satisfies tr (l + r ＝ o) = lookup tr l +F lookup tr r ≈ lookup tr o
satisfies tr (l * r ＝ o) = lookup tr l *F lookup tr r ≈ lookup tr o
satisfies tr (l ＝ₖ v)    = lookup tr l ≈ v
satisfies tr (l ＝ᵥ o)    = lookup tr l ≈ lookup tr o

satCS : ∀ {n} → Trace n → ConstraintSystem n → Set
satCS tr = All (satisfies tr)

module _ where
  open import Data.List using () renaming (_++_ to _++L_)
  open import Data.List.Relation.Unary.All.Properties

  satCS-++ : ∀ {n} → (tr : Trace n) (cs₁ : ConstraintSystem n) {cs₂ : ConstraintSystem n} → satCS tr (cs₁ ++L cs₂) → satCS tr cs₁ × satCS tr cs₂ 
  satCS-++ tr cs₁ = ++⁻ cs₁

extraVars : ∀ {m n} → Circuit m n → ℕ
extraVars (const v)   = 0
extraVars add         = 0
extraVars mul         = 0
extraVars isZero      = 4
extraVars eq0         = 0
extraVars neq0        = 2
extraVars empty       = 0
extraVars id          = 0
extraVars copy        = 0
extraVars discard     = 0
extraVars swap        = 0
extraVars (seq {n = n} c₁ c₂) = n + extraVars c₁ + extraVars c₂
extraVars (par c₁ c₂) = extraVars c₁ + extraVars c₂

totVars : ∀ {m n} → Circuit m n → ℕ
totVars {m} {n} c = m + n + extraVars c

data WhatVar (i o p : ℕ) : Set where
  inv :  (iv : Fin i ) → WhatVar i o p
  outv : (ov : Fin o) → WhatVar i o p
  priv : (pv : Fin p) → WhatVar i o p

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

postulate
  WhatVar≃Fin : ∀ i o p → WhatVar i o p ≃ Fin (i + o + p)

module _ {i oi o′ p p′ : ℕ} where
  private
    WVF  = WhatVar≃Fin i oi p
    WVF′ = WhatVar≃Fin oi o′ p′
    WVFs = WhatVar≃Fin i o′ (oi + p + p′)

  remap→seq₁ : Fin (i + oi + p)
    → Fin (i + o′ + (oi + p + p′))
  remap→seq₁ v = WVFs .to (whatvar (WVF .from v))
    where
      whatvar : WhatVar i oi p → WhatVar i o′ (oi + p + p′) 
      whatvar (inv iv)  = inv iv
      whatvar (outv oiv) = priv (oiv ↑ˡ p ↑ˡ p′)
      whatvar (priv pv) = priv ((oi ↑ʳ pv) ↑ˡ p′)

  remap→seq₂ : Fin (oi + o′ + p′)
    → Fin (i + o′ + (oi + p + p′))
  remap→seq₂ v = WVFs .to (whatvar (WVF′ .from v))
    where
      whatvar : WhatVar oi o′ p′ → WhatVar i o′ (oi + p + p′) 
      whatvar (inv oiv)  = priv (oiv ↑ˡ p ↑ˡ p′)
      whatvar (outv ov) = outv ov
      whatvar (priv pv) = priv (oi + p ↑ʳ pv)

module _ {i i′ o o′ p p′ : ℕ} where
  private
    WVF  = WhatVar≃Fin i o p
    WVF′ = WhatVar≃Fin i′ o′ p′
    WVFp = WhatVar≃Fin (i + i′) (o + o′) (p + p′)
  
  remap→par₁ : Fin (i + o + p)
    → Fin ((i + i′) + (o + o′) + (p + p′))
  remap→par₁ v = WVFp .to (whatvar (WVF .from v))
    where
      whatvar : WhatVar i o p → WhatVar (i + i′) (o + o′) (p + p′)
      whatvar (inv iv)  = inv  (iv ↑ˡ i′)
      whatvar (outv ov) = outv (ov ↑ˡ o′)
      whatvar (priv pv) = priv (pv ↑ˡ p′)

  remap→par₂ : Fin (i′ + o′ + p′)
    → Fin ((i + i′) + (o + o′) + (p + p′))
  remap→par₂ v = WVFp .to (whatvar (WVF′ .from v))
    where
      whatvar : WhatVar i′ o′ p′ → WhatVar (i + i′) (o + o′) (p + p′)
      whatvar (inv iv)  = inv  (i ↑ʳ iv)      
      whatvar (outv ov) = outv (o ↑ʳ ov)      
      whatvar (priv pv) = priv (p ↑ʳ pv)      

remapConstraint : ∀ {m n} → (remf : Fin m → Fin n)
  → Constraint m → Constraint n
remapConstraint f (l + r ＝ o) = (f l + f r ＝ f o)    
remapConstraint f (l * r ＝ o) = (f l * f r ＝ f o)    
remapConstraint f (l ＝ₖ v)    = (f l ＝ₖ v)       
remapConstraint f (l ＝ᵥ o)    = (f l ＝ᵥ f o)

remapCS : ∀ {m n} → (remf : Fin m → Fin n)
  → ConstraintSystem m → ConstraintSystem n
remapCS f = Data.List.map (remapConstraint f)

module _ where
  open import Data.List using () renaming ([] to []L; _∷_ to _∷L_; _++_ to _++L_)

  -- Convention/invariant: the outputs are the first variables, the inputs are the following
  Circuit→CS : ∀ {m} {n} (circ : Circuit m n) → ConstraintSystem (totVars circ) 
  Circuit→CS (const v) = (# 0 ＝ₖ v) ∷L []L
  Circuit→CS add = (# 0 + # 1 ＝ # 2) ∷L []L
  Circuit→CS mul = (# 0 * # 1 ＝ # 2) ∷L []L
  Circuit→CS isZero =
    let
      x   = # 0
      z   = # 1
      k₀  = # 2
      k₁  = # 3
      y   = # 4
      exy = # 5
    in
       k₀ ＝ₖ 0F ∷L
      (k₁ ＝ₖ 1F ∷L
      (x * z ＝ k₀ ∷L
      (x * y ＝ exy ∷L
      (exy + z ＝ k₁ ∷L
      (z * z ＝ z ∷L []L)))))
  Circuit→CS eq0 = (# 0 ＝ₖ 0F) ∷L []L
  Circuit→CS neq0 =
    let
      x   = # 0
      y   = # 1
      exy = # 2
    in
      (x * y ＝ exy ∷L
      (exy ＝ₖ 1F ∷L []L))
  Circuit→CS empty = []L
  Circuit→CS id = (# 0 ＝ᵥ # 1) ∷L []L
  Circuit→CS copy = (# 1 ＝ᵥ # 0) ∷L ((# 2 ＝ᵥ # 0) ∷L []L)
  Circuit→CS discard = []L
  Circuit→CS swap = # 1 ＝ᵥ # 2 ∷L (# 0 ＝ᵥ # 3 ∷L []L)
  Circuit→CS (seq {n = n} c₁ c₂) = let
      cs₁ = Circuit→CS c₁
      cs₂ = Circuit→CS c₂
    in remapCS remap→seq₁ cs₁ ++L remapCS remap→seq₂ cs₂
  Circuit→CS (par c₁ c₂) = let
      cs₁ = Circuit→CS c₁
      cs₂ = Circuit→CS c₂
    in
      remapCS remap→par₁ cs₁ ++L remapCS remap→par₂ cs₂

_≈v_ : ∀ {n} → (v₁ : Vec Val n) → (v₂ : Vec Val n) → Set
v₁ ≈v v₂ = AllV (uncurry _≈_) (zip v₁ v₂) 

_j≈v_ : ∀ {n} → (mv₁ : Maybe (Vec Val n)) → (mv₂ : Maybe (Vec Val n)) → Set
_j≈v_ = Pointwise _≈v_

open import Relation.Binary.Reasoning.Setoid F-setoid

soundness : ∀ m n
  (circ : Circuit m n)
  (inp : Vec Val m)
  (out : Vec Val n)
  (priv : Vec Val (extraVars circ))
  → satCS ((inp ++ out) ++ priv) (Circuit→CS circ)
  → ⟦ circ ⟧ inp j≈v just out
soundness .0 .1 (const v) [] (o ∷ []) [] (sat₀ All.∷ _) = Pointwise.just (sym sat₀ AllV.∷ AllV.[])
soundness .2 .1 add (x₁ ∷ x₂ ∷ []) (z ∷ []) priv₁ (sat₀ All.∷ _) = Pointwise.just (sat₀ AllV.∷ AllV.[])
soundness .2 .1 mul (x₁ ∷ x₂ ∷ []) (z ∷ []) priv₁ (sat₀ All.∷ _) = Pointwise.just (sat₀ AllV.∷ AllV.[])
soundness .1 .1 isZero (x ∷ []) (z ∷ []) (k₀ ∷ k₁ ∷ y ∷ exy ∷ []) (
    k₀≈0      All.∷
    k₁≈1      All.∷
    x*z≈k₀    All.∷
    x*y≈exy   All.∷
    exy+z≈k₁  All.∷
    z*z≈z     All.∷
              All.[]
  ) = Pointwise.just (goal AllV.∷ AllV.[])
  where
    open Field F hiding (_≈_; dec≈; sym)
    goal : ite≈0F x 1F 0F ≈ z
    goal with (dec≈ x 0F)
    ... | .true  because ofʸ x≈0 =
      let xy≈0 : exy ≈ 0F
          xy≈0 = begin
              exy
            ≈⟨ sym x*y≈exy ⟩
              x *F y 
            ≈⟨ *-congʳ x≈0 ⟩
              0F *F y
            ≈⟨ zeroˡ y ⟩
              0F
            ∎
      in begin
        1F
      ≈⟨ sym k₁≈1 ⟩
        k₁
      ≈⟨ sym exy+z≈k₁ ⟩
        exy +F z
      ≈⟨ +-congʳ xy≈0 ⟩
        0F +F z
      ≈⟨ +-identityˡ z ⟩
        z
      ∎
    ... | .false because ofⁿ ¬x≈0 =
      let
        x⁻¹ , isInv = hasInverse x ¬x≈0
      in begin
        0F
      ≈⟨ sym (zeroʳ x⁻¹) ⟩
        x⁻¹ *F 0F
      ≈⟨ *-congˡ (sym k₀≈0) ⟩
        x⁻¹ *F k₀
      ≈⟨ *-congˡ (sym x*z≈k₀) ⟩
        x⁻¹ *F (x *F z)
      ≈⟨ sym (*-assoc x⁻¹ x z) ⟩
        (x⁻¹ *F x) *F z
      ≈⟨ *-congʳ (*-comm x⁻¹ x) ⟩
        (x *F x⁻¹) *F z
      ≈⟨ *-congʳ isInv ⟩
        1F *F z
      ≈⟨ *-identityˡ z ⟩
        z
      ∎
soundness .1 .0 eq0 inp out priv₁ sat = {! !}
soundness .1 .0 neq0 inp out priv₁ sat = {! !}
soundness .0 .0 empty inp out priv₁ sat = {! !}
soundness .1 .1 id inp out priv₁ sat = {! !}
soundness .1 .2 copy inp out priv₁ sat = {! !}
soundness .1 .0 discard inp out priv₁ sat = {! !}
soundness .2 .2 swap inp out priv₁ sat = {! !}
soundness m p (seq {n = n} circ₁ circ₂) inp₁ out₂ oi-pr₁-pr₂ sat = let
    npr₁ = extraVars circ₁
    npr₂ = extraVars circ₂
    (oi-pr₁ , pr₂ , oi-pr₁-pr₂-eq) = splitAt (n + npr₁) oi-pr₁-pr₂
    (oi , pr₁ , oi-pr₁-eq) = splitAt n oi-pr₁
    (sat-rm₁ , sat-rm₂) = satCS-++ ((inp₁ ++ out₂) ++ oi-pr₁-pr₂) (remapCS remap→seq₁ (Circuit→CS circ₁)) sat
    ihcirc₁ = soundness m n circ₁ inp₁ oi pr₁ {! !}
    ihcirc₂ = soundness n p circ₂ oi out₂ pr₂ {! !}
  in {! sat!}
soundness .(_ + _) .(_ + _) (par circ circ₁) inp out priv₁ sat = {! !}

