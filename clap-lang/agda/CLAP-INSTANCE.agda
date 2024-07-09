open import Data.Integer renaming (_+_ to _+ᵢ_ ; _*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
   using ( _≤ᵇ_ ; ℤ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )


module CLAP-INSTANCE (modulus : ℤ)  where

open import Data.Unit hiding (_≟_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_ ; _≤?_; z≤n; s≤s; _+_; _*_ ; _≟_ ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.List renaming (map to mapₗ ; find to findₗ ; zip to zipₗ ; concat to concatₗ) hiding (fromMaybe)
open import Data.Bool hiding (_≤_ ; _≤?_) renaming (_≟_ to _≟b_)

open import Data.List.Membership.DecPropositional {_} {ℕ}  _≟_
open import Data.List.Relation.Unary.Unique.DecPropositional {_} {ℕ} _≟_
open import Data.List.Properties
open import Relation.Nullary

open import EGCD modulus

open import Extra
open import Data.Maybe renaming (_>>=_ to _>>=m_)

open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl ; decSetoid)

open import Data.List.Relation.Unary.Any



Field : Set
Field = ℤ

zeroF : Field
zeroF = ᵢ+ 0

data Gate : Set where
 const : ℤ → Gate
 add   : ℕ → ℕ → Gate
 eq0   : ℕ → Gate

data Expr : Set where
  _+_＝_ : ℕ → ℕ → ℕ → Expr
  _＝c_  : ℕ → ℤ → Expr

extInps-gate   : Gate → ℕ × List ℕ → ℕ × List ℕ
extInps-gate (const x) (n ,, l) = suc n ,, (n ∷ l)
extInps-gate (add x x₁) (n ,, l) = suc n ,, (n ∷ l)
extInps-gate (eq0 x) (n ,, l) = n ,, l

WellFormedGate : Gate → ℕ × List ℕ → Set
WellFormedGate (const x) (fst ,, snd) = ⊤
WellFormedGate (add x₁ x₂) (n ,, l) = x₁ ∈ l × x₂ ∈ l × (suc x₁ ≤ n) × (suc x₂ ≤  n)
WellFormedGate (eq0 x) (n ,, l) = x ∈ l × (suc x ≤ n)

genTraceGate : Gate → List Field → List Field
genTraceGate (const x) t = t ++ [ x %% modulus ]
genTraceGate (add x x₁) t = t ++ [ (lkp-gen zeroF x t +ᵢ lkp-gen zeroF x₁ t) %% modulus ]
genTraceGate (eq0 x) t = t

genTraceAGate  : Gate → Bool × List Field → Bool × List Field
genTraceAGate (const x) (b ,, t) = b ,, t ++ [ x  %% modulus ]
genTraceAGate (eq0 x) (b ,, t) = b ∧ mb2b ((lkpmb x t) >>=m λ xv → just (xv  ≡ᵇz ((ᵢ+ 0) %% modulus) ))  ,, t
genTraceAGate (add x x₁) (b ,, t) = b ,, t ++ [ (lkp-gen zeroF x t +ᵢ lkp-gen zeroF x₁ t) %% modulus ]

genCS-gate     : Gate → ℕ × List Expr → ℕ × List Expr
genCS-gate (const x) (n ,, snd) = suc n ,, n ＝c x ∷ snd
genCS-gate (add x x₁) (fst ,, snd) = suc fst ,, x + x₁ ＝ fst ∷ snd
genCS-gate (eq0 x) (fst ,, snd) = fst ,, x ＝c (ᵢ+ 0) ∷ snd

WFCS-expr      : Expr → ℕ → Set
WFCS-expr (x + x₁ ＝ x₂) n = (suc x ≤ n) × (suc x₁ ≤ n) × (suc x₂ ≤ n)
WFCS-expr (x ＝c x₁) n =  (suc x ≤ n) 

satCS'-expr    : Expr → List Field → Bool
satCS'-expr ((x + x₁ ＝ x₂)) trace =
   mb2b (lkpmb x trace >>=m (λ xc → lkpmb x₁ trace >>=m λ yc → lkpmb x₂ trace >>=m λ zc
    → just (isYes ((xc +ᵢ yc) %% modulus ≟z zc))))
satCS'-expr ((x ＝c x₁)) trace =
  mb2b (lkpmb x trace >>=m 
       (λ xv → just (xv ≡ᵇz (x₁ %% modulus))))

import CLAP-BASE
module CLAP-BASE-ℤ = CLAP-BASE 
  Field 
  zeroF 
  Gate 
  Expr
  extInps-gate   
  WellFormedGate 
  genTraceGate   
  genTraceAGate  
  genCS-gate     
  WFCS-expr      
  satCS'-expr    
open CLAP-BASE-ℤ

-- PROPERTIES

open import Data.Nat.Properties
extInpsMonotonic-gate : (c : Gate) 
    → (pos : ℕ × List ℕ) 
    → proj₁ pos ≤ proj₁ (extInps-gate c pos)
extInpsMonotonic-gate (const x) pos = n≤1+n _
extInpsMonotonic-gate (add x x₁) pos = n≤1+n _
extInpsMonotonic-gate (eq0 x) pos = ≤-refl


genCSMonotonic-gate : (c : Gate) 
    → (cs : CS)  
    → proj₁ cs ≤ proj₁ (genCS-gate c cs)
genCSMonotonic-gate (const x) cs = n≤1+n _
genCSMonotonic-gate (add x x₁) cs = n≤1+n _
genCSMonotonic-gate (eq0 x) cs = ≤-refl


genCS-extInps-agree-gate : (c : Gate) 
   → (cs : CS) 
   → (pos : ℕ × List ℕ)  
   → proj₁ cs ≡ proj₁ pos 
   → proj₁ (genCS-gate c cs)
       ≡ proj₁ (extInps-gate c pos)
genCS-extInps-agree-gate (const x) (.(proj₁ pos) ,, snd) pos refl = refl
genCS-extInps-agree-gate (add x x₁) (.(proj₁ pos) ,, snd) pos refl = refl
genCS-extInps-agree-gate (eq0 x) (.(proj₁ pos) ,, snd) pos refl = refl




   
satCS'-weaken-gate : (c : Gate) → (cs : CS) → (trace : List Field) 
   → satCS' (proj₂ (genCS-gate c cs)) trace ≡ true
   → satCS' (proj₂ cs) trace ≡ true
satCS'-weaken-gate (const x) cs trace p = and-rgt _ _ p
satCS'-weaken-gate (add x x₁) cs trace p = and-rgt _ _ p
satCS'-weaken-gate (eq0 x) cs trace p = and-rgt _ _ p


extInps-genTrace-gate : (c : Gate) 
   → (trace : List Field) 
   → (pos : ℕ × List ℕ) 
   → proj₁ pos ≡ length trace
   → proj₁ (extInps-gate c pos) ≡ (length (genTraceGate c trace))
extInps-genTrace-gate (const x) t (.(length t) ,, snd) refl rewrite mlength-++ t  [ x %% modulus ]
 | Data.Nat.Properties.+-comm (length t) 1 = Eq.cong suc refl 
extInps-genTrace-gate (add x x₁) t pos pr rewrite mlength-++ t  [ (lkp x t +ᵢ lkp x₁ t) %% modulus ]
 | Data.Nat.Properties.+-comm (length t) 1 = Eq.cong suc pr 
extInps-genTrace-gate (eq0 x) t pos eq = eq
   
extInps-genTraceA-gate : (c : Gate) 
    → (trace : Bool × List Field) 
    → (pos : ℕ × List ℕ)
    → proj₁ pos ≡ length (proj₂ trace)
    → proj₁ (extInps-gate c pos) ≡ (length (proj₂ (genTraceAGate c trace)))
extInps-genTraceA-gate (eq0 x) trace pos pr = pr
extInps-genTraceA-gate (const x) trace pos pr rewrite mlength-++ (proj₂ trace)  [ x %% modulus ]
 | Data.Nat.Properties.+-comm (length (proj₂ trace)) 1 = Eq.cong suc pr 
extInps-genTraceA-gate (add x x₁) trace pos pr
 rewrite mlength-++ (proj₂ trace)  [ (lkp x (proj₂ trace) +ᵢ lkp x₁ (proj₂ trace)) %% modulus ]
 | Data.Nat.Properties.+-comm (length (proj₂ trace)) 1 = Eq.cong suc pr 
  
lkp-const : (trace : List ℤ) → (n : ℕ) → (x : ℤ) → length trace ≡ n
  → lkp n (genTraceGate (const x) trace) ≡ x %% modulus
lkp-const [] zero x p = refl
lkp-const (x₁ ∷ t) (suc n) x p = lkp-const t n x (Eq.cong Data.Nat.pred p)

lkp-p : (n : ℕ) → (t : List ℤ) → (x : ℤ) → length t ≡ n → lkp n (t ++ [ x ]) ≡ x
lkp-p zero [] x pr = refl
lkp-p (suc n) (x₁ ∷ t) x pr = lkp-p n t x (Eq.cong Data.Nat.pred pr)

lkp-add : (trace : List ℤ) → (n a b : ℕ) → length trace ≡ n
  → lkp n (genTraceGate (add a b) trace) ≡ (lkp a trace +ᵢ lkp b trace) %% modulus
lkp-add t n a b p = lkp-p n t  ((lkp a (t) +ᵢ lkp b t) %% modulus) p  

ext-lkp : (trace1 trace2 ext : List ℤ) → (x : ℕ)
  → length trace1 ≡ length trace2
  → lkp x trace1 ≡ lkp x trace2
  → lkp x (trace1 ++ ext) ≡ lkp x (trace2 ++ ext)
ext-lkp  [] [] ext x p1 p2 = refl
ext-lkp (x₁ ∷ trace1) (x₂ ∷ trace2) ext zero p1 p2 = p2
ext-lkp (x₁ ∷ trace1) (x₂ ∷ trace2) ext (suc x) p1 p2 = ext-lkp trace1 trace2 ext x (Eq.cong Data.Nat.pred p1) p2

ext-projPos : (outs : List ℕ) → (trace1 trace2 ext : List ℤ)
  → length trace1 ≡ length trace2
  → projPos outs trace1 ≡ projPos outs trace2
  → projPos outs (trace1 ++ ext) ≡ projPos outs (trace2 ++ ext)
ext-projPos [] (trace1) (trace2) ext prf eq = refl
ext-projPos (x₂ ∷ outs) (trace1) (trace2) ext prf eq rewrite ext-projPos outs trace1 trace2 ext prf (Eq.cong (Data.List.drop 1) eq) = Eq.cong (λ x → x ∷ projPos outs (trace2 ++ ext)) q
  where
     w : lkp x₂ trace1 ≡ lkp x₂ trace2
     w = Eq.cong (λ x → fromMaybe (ᵢ+ 0) (Data.List.head x)  )  eq

     q : lkp x₂ (trace1 ++ ext) ≡ lkp x₂ (trace2 ++ ext)
     q = ext-lkp trace1 trace2 ext  x₂ prf w



proj-lem : (x : ℕ)
 → (pos : List ℕ)
 → (t1 t2 : List ℤ)
 → x ∈ pos → projPos pos t1 ≡ projPos pos t2 → lkp x t1 ≡ lkp x t2
proj-lem x .(x ∷ _) t1 t2 (here refl) prf = Eq.cong (λ x → fromMaybe zeroF (Data.List.head x)  ) prf
proj-lem x .(_ ∷ _) t1 t2 (there xin) prf = proj-lem x _  t1 t2  xin (Eq.cong (Data.List.drop 1) prf)

proj-cong-gate : (c : Gate) 
    → (pos : ℕ × List ℕ) 
    → (trace1 trace2 : List Field)
    → WellFormedGate c pos
    → projPos (proj₂ pos) trace1  ≡ projPos (proj₂ pos) trace2
    → length trace1 ≡ proj₁ pos
    → length trace2 ≡ proj₁ pos
    → projPos (proj₂ (extInps-gate c pos)) (genTraceGate c trace1) 
        ≡ projPos (proj₂ (extInps-gate c pos)) (genTraceGate c trace2)
proj-cong-gate (const x) pos trace1 trace2 wf hyp a b rewrite lkp-const trace1  (proj₁ pos) x a
  | lkp-const trace2  (proj₁ pos) x b =  Eq.cong ((λ l → x %% modulus ∷ l)) (ext-projPos  (proj₂ pos) trace1 trace2 _ (Eq.trans a (Eq.sym b)) hyp)
 --
proj-cong-gate (eq0 x) pos trace1 trace2 wf hyp a b = hyp
proj-cong-gate (add x x₁) pos trace1 trace2 (wf1 ,, wf2) hyp a b
 rewrite lkp-add trace1 (proj₁ pos) x x₁ a
 | lkp-add trace2 (proj₁ pos) x x₁ b
 | proj-lem x (proj₂ pos) trace1 trace2  wf1 hyp
 | proj-lem x₁ (proj₂ pos) trace1 trace2  (proj₁ wf2) hyp
   =  Eq.cong (λ l →  _ ∷ l) (ext-projPos (proj₂ pos) trace1 trace2 _ (Eq.trans a (Eq.sym b)) hyp)


posCorr-extInps-gate : (c : Gate)
    → (pos : ℕ × List ℕ) 
    → WellFormedGate c pos
    → PosCorrect pos 
    → PosCorrect (extInps-gate c pos)
posCorr-extInps-gate (const x₁) pos tt pc .(proj₁ pos) (here refl) = ≤-refl
posCorr-extInps-gate (const x₁) pos tt pc x (there px) = m≤n⇒m≤1+n (pc x px)
posCorr-extInps-gate (add x₁ x₂) pos wf pc .(proj₁ pos) (here refl) = ≤-refl
posCorr-extInps-gate (add x₁ x₂) pos wf pc x (there y) = m≤n⇒m≤1+n (pc x y)
posCorr-extInps-gate (eq0 x₁) pos wf pc x y = pc x y

  
genCS-WFCS-weak-expr : (n : ℕ) →  (cs : Expr) → WFCS-expr cs n → WFCS-expr cs (suc n)
genCS-WFCS-weak-expr n ((x + x₁ ＝ x₂)) (a ,, b ,, c ) = m≤n⇒m≤1+n a ,, m≤n⇒m≤1+n b ,, m≤n⇒m≤1+n c 
genCS-WFCS-weak-expr n ((x ＝c x₁)) wfcs = m≤n⇒m≤1+n (wfcs) 


genCS-WFCS-weak : (n : ℕ) →  (cs : List Expr) → WFCS cs n → WFCS cs (suc n)
genCS-WFCS-weak n [] wfcs = tt
genCS-WFCS-weak n (c ∷ cs) wfcs = genCS-WFCS-weak-expr n c (proj₁ wfcs)  ,, genCS-WFCS-weak n cs (proj₂ wfcs)

genCS-WFCS-gate : (c : Gate) 
   → (pos : ℕ × List ℕ) 
   → (cs : CS)
   → WellFormedGate c pos
   → proj₁ pos ≡ proj₁ cs
   → WFCS (proj₂ cs) (proj₁ cs)
   → WFCS (proj₂ (genCS-gate c cs)) (proj₁ (genCS-gate c cs))
genCS-WFCS-gate (const x) pos cs wfc wfcs pr =  s≤s Data.Nat.Properties.≤-refl ,, genCS-WFCS-weak _ _  pr
genCS-WFCS-gate (add x x₁) (.(proj₁ cs) ,, snd) cs wfc@(a ,, b ,, c ,, d)  refl pr = (m≤n⇒m≤1+n c ,, m≤n⇒m≤1+n d ,, ≤-refl)  ,, genCS-WFCS-weak _ _ pr 
genCS-WFCS-gate (eq0 x) (.(proj₁ cs) ,, snd) cs wfc refl pr = proj₂ wfc ,, pr

lkpmb=eq : (x n : ℕ) → (trace : List ℤ) →  suc x ≤ n → lkpmb x trace ≡ lkpmb x (take n trace)
lkpmb=eq x .(suc _) [] (s≤s prf) = refl
lkpmb=eq zero .(suc _) (x₁ ∷ trace) (s≤s prf) = refl
lkpmb=eq (suc x) .(suc _) (x₁ ∷ trace) (s≤s prf) = lkpmb=eq x _ trace prf

lemm2-expr : (exprs : Expr)(n : ℕ) → WFCS-expr exprs n → (trace : List Field)
    → satCS'-expr exprs trace ≡ satCS'-expr exprs (take n trace)       
lemm2-expr ((x + x₁ ＝ x₂)) n (a ,, b ,, c) trace rewrite
  lkpmb=eq x n trace a | lkpmb=eq x₁ n trace b | lkpmb=eq x₂ n trace c  = refl
lemm2-expr ((x ＝c x₁) ) n a trace rewrite 
 lkpmb=eq x n trace a =  refl


open import CLAP-PROPERTIES
  Field 
  zeroF 
  Gate 
  Expr
  extInps-gate   
  WellFormedGate 
  genTraceGate   
  genTraceAGate  
  genCS-gate     
  WFCS-expr      
  satCS'-expr    


open SoundnessAndCompletenessCompose
  extInpsMonotonic-gate
  genCSMonotonic-gate
  genCS-extInps-agree-gate
  genCS-WFCS-gate
  satCS'-weaken-gate
  extInps-genTrace-gate
  extInps-genTraceA-gate
  proj-cong-gate
  posCorr-extInps-gate
  genCS-WFCS-weak-expr 
  lemm2-expr


