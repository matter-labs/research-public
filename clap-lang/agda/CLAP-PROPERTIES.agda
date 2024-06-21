{-# OPTIONS --warning=noModuleDoesntExport #-}
open import Data.Integer renaming (_+_ to _+ᵢ_ ; _*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
  using (_≤ᵇ_ ; ℤ ; _+ᵢ_ ; _*ᵢ_ ; _≟z_ ; Sign ; ᵢ+_ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )
module CLAP-PROPERTIES (modulus : ℤ) where

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


genTraceA : Circuit → Bool × List ℤ → Bool × List ℤ
genTraceA empty (b ,, t) = b ,, t
genTraceA (const x) (b ,, t) = b ,, t ++ [ x  %% modulus ]
genTraceA (eq0 x)   (b ,, t) = b ∧ mb2b ((lkpmb x t) >>=m λ xv → just (xv  ≡ᵇz ((ᵢ+ 0) %% modulus) ))  ,, t
genTraceA (add x x₁) (b ,, t) = b ,, t ++ [ (lkp x t +ᵢ lkp x₁ t) %% modulus ]
genTraceA (seq c c₁) bt = genTraceA c₁ (genTraceA c bt)
genTraceA _ = {!!}


lemm1-weak : (n : ℕ) →  (cs : List Expr) → WFCS cs n → WFCS cs (suc n)
lemm1-weak n [] wfcs = tt
lemm1-weak n ((x + x₁ ＝ x₂) ∷ cs) (a ,, b ,, c ,, d) = Data.Nat.Properties.m≤n⇒m≤1+n a ,, Data.Nat.Properties.m≤n⇒m≤1+n b ,, Data.Nat.Properties.m≤n⇒m≤1+n c ,, lemm1-weak n cs d
lemm1-weak n ((x * x₁ ＝ x₂) ∷ cs) (a ,, b ,, c ,, d) = Data.Nat.Properties.m≤n⇒m≤1+n a ,, Data.Nat.Properties.m≤n⇒m≤1+n b ,, Data.Nat.Properties.m≤n⇒m≤1+n c ,, lemm1-weak n cs d
lemm1-weak n ((x ＝c x₁) ∷ cs) wfcs = Data.Nat.Properties.m≤n⇒m≤1+n (proj₁ wfcs) ,, lemm1-weak n cs (proj₂ wfcs)



aux : (c : Circuit) → (cs : CS) → (pos : ℕ × List ℕ) → proj₁ cs ≡ proj₁ pos →
 (proj₁ (genCS c cs)) ≡  proj₁ (extInps c pos)
aux empty pr pos pp = pp
aux (const x) (.(proj₁ pos) ,, snd) pos refl = refl
aux (eq0 x) (.(proj₁ pos) ,, snd) pos refl = refl
aux (add x x₁) (.(proj₁ pos) ,, snd) pos refl = refl
aux (seq c c₁) (.(proj₁ pos) ,, snd) pos refl   = aux c₁ _ _ (aux c _ pos refl)
aux _ = {!!}

lemm1 : (c : Circuit) → (pos : ℕ × List ℕ) → (cs : CS)
   → WellFormedCircuit c pos
   → proj₁ pos ≡ proj₁ cs
   → WFCS (proj₂ cs) (proj₁ cs)
   → WFCS (proj₂ (genCS c cs)) (proj₁ (genCS c cs))
lemm1 empty pos cs wfc wfcs pr = pr
lemm1 (const x) pos cs wfc wfcs pr = s≤s Data.Nat.Properties.≤-refl ,, lemm1-weak _ _  pr
lemm1 (eq0 x) pos cs wfc refl pr =  proj₂ wfc ,, pr
lemm1 (add x x₁) (.(proj₁ cs) ,, snd) cs wfc@(a ,, b ,, c ,, d) refl pr = Data.Nat.Properties.m≤n⇒m≤1+n c ,, Data.Nat.Properties.m≤n⇒m≤1+n d ,, Data.Nat.Properties.≤-refl ,, lemm1-weak _ _  pr
lemm1 (seq c c₁) pos@(.(proj₁ cs) ,, snd) cs wfc refl wfcs = lemm1 c₁ _  (genCS c cs) (proj₂ wfc) (Eq.sym (aux c  cs pos refl) ) (lemm1 c pos cs (proj₁ wfc) refl wfcs)
lemm1 _ = {!!}


lkpmb=eq : (x n : ℕ) → (trace : List ℤ) →  suc x ≤ n → lkpmb x trace ≡ lkpmb x (take n trace)
lkpmb=eq x .(suc _) [] (s≤s prf) = refl
lkpmb=eq zero .(suc _) (x₁ ∷ trace) (s≤s prf) = refl
lkpmb=eq (suc x) .(suc _) (x₁ ∷ trace) (s≤s prf) = lkpmb=eq x _ trace prf


lemm2 : (exprs : List Expr)(n : ℕ) → WFCS exprs n → (trace : List ℤ)
  → satCS' exprs trace ≡ satCS' exprs (take n trace)
lemm2 [] n wf trace = refl
lemm2 ((x + x₁ ＝ x₂) ∷ exprs) n (a ,, b ,, c ,, d) trace rewrite lemm2 exprs n d trace
 | lkpmb=eq x n trace a | lkpmb=eq x₁ n trace b | lkpmb=eq x₂ n trace c  = refl
lemm2 ((x * x₁ ＝ x₂) ∷ exprs) n (a ,, b ,, c ,, d) trace rewrite lemm2 exprs n d trace
 | lkpmb=eq x n trace a | lkpmb=eq x₁ n trace b | lkpmb=eq x₂ n trace c  = refl 
lemm2 ((x ＝c x₁) ∷ exprs) n (a ,, b) trace rewrite lemm2 exprs n b trace
 | lkpmb=eq x n trace a =  refl


postulate
  and-lft : (a b : Bool) → a ∧ b ≡ true → a ≡ true
  and-rgt : (a b : Bool) → a ∧ b ≡ true → b ≡ true
  and-int : (a b : Bool) → a ≡ true → b ≡ true → a ∧ b ≡ true
  aux5 : (c : Circuit) → (cs : CS) → (trace : List ℤ) →  satCS' (proj₂ (genCS c cs)) trace ≡ true
     → satCS' (proj₂ cs) trace ≡ true
  aux7 : (cs : List Expr) → (trace suffix : List ℤ) →  satCS' cs trace ≡ true → satCS' cs (trace ++ suffix)  ≡ true
  aux8 : (x : ℕ) (y : ℤ) → (trace : List ℤ) →  length trace ≡ x → lkpmb x (trace ++ [ y ]) ≡ just y
  aux9 : (x : ℤ) → isYes (x ≟z x) ≡ true
  aux10 : (a b : ℕ) → (a ≡ᵇ b) ≡ true → a ≡ b
  aux11 : (x y : ℤ) → isYes (x ≟z y) ≡ true   → x ≡ y
  leq-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
  eq-leq : {a b : ℕ} → a ≡ b → a ≤ b
  eqb-eq : {a b : ℕ} → (a ≡ᵇ b) ≡ true → a ≡ b
  mlength-++ : {A : Set} → (l1 l2 : List A) →  length (l1 ++ l2) ≡ length l1 + length l2
  lkp=lkpmb : (x : ℕ) → (trace : List ℤ) → suc x ≤ length trace → lkpmb x trace ≡ just (lkp x trace)
  lkpmb=lkpmb : (x : ℕ) → (trace1 trace2 : List ℤ) → suc x ≤ length trace1 →  lkpmb x (trace1 ++ trace2) ≡ lkpmb x trace1
  take-drop : {A : Set} → (l : List A) → (n : ℕ) → l ≡ take n l ++ drop n l
  take-drop' :  (l : List ℤ) → (n : ℕ) → length l ≡ suc n → drop n l ≡ [ lkp n l  ]
  take-all'   : (l : List ℤ) → take (length l) l ≡ l
  take-all''   : (l1 l2 : List ℤ) → take (length l1) (l1 ++ l2) ≡ l1
  take-drop'' :  (l a b : List ℤ) → a ≡ b → l ++ a ≡ l ++ b
  take-longer :  (l : List ℤ) → (n x : ℕ) → suc x ≤ n → lkp x l ≡ lkp x (take n l)
  modmod : ∀ z → (z %% modulus) %% modulus ≡ z %% modulus

aux2 : {A : Set} →  {n m : ℕ} → n ≤ m → (l : List A) → take n (take m l) ≡ take n l
aux2 z≤n l = refl
aux2 (s≤s p) [] = refl
aux2 (s≤s p) (x ∷ l) rewrite aux2 p l = refl

aux3 : (c : Circuit) → (cs : CS) →
 (proj₁ cs) ≤ (proj₁ (genCS c cs))
aux3 empty cs = Data.Nat.Properties.≤-refl
aux3 (const x) cs = Data.Nat.Properties.n≤1+n _
aux3 (eq0 x) cs = Data.Nat.Properties.≤-refl
aux3 (add x x₁) cs = Data.Nat.Properties.n≤1+n _
aux3 (seq c c₁) cs with aux3 c cs | aux3 c₁ (genCS c cs)
... | p₁ | p₂ = Data.Nat.Properties.≤-trans p₁ p₂
aux3 _ = {!!}

aux4 : {A : Set} (n : ℕ) → (l : List A) → n ≤ length l → (length (take n l) ≡ᵇ n) ≡ true
aux4 .zero [] z≤n = refl
aux4 .zero (x ∷ l) z≤n = refl
aux4 .(suc _) (x ∷ l) (s≤s prf) = aux4 _ l prf


extInps-genTrace : (c : Circuit) → (trace : List ℤ) → (pos : ℕ × List ℕ) → proj₁ pos ≡ length trace
                     → proj₁ (extInps c pos) ≡ (length (genTrace c trace))
extInps-genTrace (eq0 x) trace pos pr = pr
extInps-genTrace empty trace pos pr = pr
extInps-genTrace (const x) trace pos pr rewrite mlength-++ trace  [ x %% modulus ]
 | Data.Nat.Properties.+-comm (length trace) 1 = Eq.cong suc pr
extInps-genTrace (add x x₁) trace pos pr
 rewrite mlength-++ trace  [ (lkp x trace +ᵢ lkp x₁ trace) %% modulus ]
 | Data.Nat.Properties.+-comm (length trace) 1 = Eq.cong suc pr -- 
extInps-genTrace (seq c c₁) trace pos pr = extInps-genTrace c₁ (genTrace c trace) _ (extInps-genTrace c trace pos pr)
extInps-genTrace _ = {!!}

extInps-genTraceA : (c : Circuit) → (trace : Bool × List ℤ) → (pos : ℕ × List ℕ)
   → proj₁ pos ≡ length (proj₂ trace)
   → proj₁ (extInps c pos) ≡ (length (proj₂ (genTraceA c trace)))
extInps-genTraceA empty trace pos pr = pr
extInps-genTraceA (eq0 x) trace pos pr = pr
extInps-genTraceA (const x) trace pos pr rewrite mlength-++ (proj₂ trace)  [ x %% modulus ]
 | Data.Nat.Properties.+-comm (length (proj₂ trace)) 1 = Eq.cong suc pr 
extInps-genTraceA (add x x₁) trace pos pr
 rewrite mlength-++ (proj₂ trace)  [ (lkp x (proj₂ trace) +ᵢ lkp x₁ (proj₂ trace)) %% modulus ]
 | Data.Nat.Properties.+-comm (length (proj₂ trace)) 1 = Eq.cong suc pr 
extInps-genTraceA (seq c c₁) trace pos pr = extInps-genTraceA c₁ (genTraceA c trace) _ (extInps-genTraceA c trace pos pr)
extInps-genTraceA _ = {!!}




postulate
 -- I assume this projects the "public" part of the trace
 projPos : ℕ × List ℕ → List ℤ → List ℤ


proj-cong : (c : Circuit) → (pos : ℕ × List ℕ) → (trace1 trace2 : List ℤ)
  → WellFormedCircuit c pos
  → projPos pos trace1  ≡ projPos pos trace2
  → projPos (extInps c pos) (genTrace c trace1) ≡ projPos (extInps c pos) (genTrace c trace2)
proj-cong empty pos trace1 trace2 wf hyp = hyp
proj-cong (const x) pos trace1 trace2 wf hyp rewrite hyp = {!refl!}
proj-cong (eq0 x) pos trace1 trace2 wf hyp = hyp
proj-cong (add x x₁) pos trace1 trace2 wf hyp = {!!}
proj-cong (seq c c₁) pos trace1 trace2 wf hyp =
   proj-cong c₁  _ (genTrace c trace1) (genTrace c trace2) (proj₂ wf)
                   (proj-cong c pos trace1 trace2  (proj₁ wf) hyp  )
proj-cong _ = {!!}

brr : (b : Bool) → ¬ b ≡ true → b ≡ false
brr false q = refl
brr true q with q refl
... | ()

brr2 : (a b : Bool) → a ∧  b ≡ false → a ≡ false ⊎ b ≡ false
brr2 false b pr1 = inj₁ refl
brr2 true false pr1 = inj₂ refl


brr3 : (a b  : Bool) → a ∧ (b ∧  false) ≡ false
brr3 false false = refl
brr3 false true = refl
brr3 true false = refl
brr3 true true = refl

brr4 : (a b c : Bool) → a ∧ b ∧ c ≡ (a ∧ c) ∧ b
brr4 false b c = refl
brr4 true false false = refl
brr4 true false true = refl
brr4 true true false = refl
brr4 true true true = refl


completeness : (c : Circuit)
  → (trace : Bool × List ℤ)  -- Maybe List ℤ?
  → (cs : CS)
  → (pos : ℕ × List ℕ)
  → WellFormedCircuit c pos
  → WFCS (proj₂ cs) (proj₁ pos)
  → length (proj₂ trace) ≡ proj₁ pos
  → (proj₁ pos) ≡ proj₁ cs
  → satCS cs (proj₂ trace) ≡ (proj₁ trace)
  → satCS (genCS c cs) (proj₂ (genTraceA c trace)) ≡ proj₁ (genTraceA c trace)
  
completeness empty trace cs (.(length (proj₂ trace)) ,, snd) wfc wfcs refl rp prop = prop
completeness (eq0 x) trace cs (.(length (proj₂ trace)) ,, snd) wfc wfcs refl rp prop rewrite (Eq.sym prop)
 = brr4 ((foldr (λ _ → suc) 0 (proj₂ trace) ≡ᵇ proj₁ cs)) _ _  

completeness (const x) trace cs@(fst ,, snd) pos wfc wfcs pr rp prop with satCS cs (proj₂ trace) ≟b true
completeness (const x) trace (fst ,, snd) pos wfc wfcs pr  rp prop | .true because ofʸ a
  rewrite a 
  | mlength-++ (proj₂ trace) [ x %% modulus ]
  | Data.Nat.Properties.+-comm  (length (proj₂ trace)) 1
  | Eq.sym prop
  | and-lft (length (proj₂ trace) ≡ᵇ fst) _ a
  | aux7 snd (proj₂ trace) [ x %% modulus ] (and-rgt _ _ a)
  | aux8 fst (x %% modulus) (proj₂ trace) (aux10 _ _ (and-lft _ _ a))
  | modmod x 
  | aux9 (x %% modulus) = refl
completeness (const x) trace (fst ,, snd) pos wfc wfcs pr rp  prop | .false because ofⁿ a rewrite brr _ a | Eq.sym prop with brr2 _ (satCS' snd (proj₂ trace)) (brr _ a)
... | inj₁ pr1 rewrite mlength-++ (proj₂ trace) [ x %% modulus ]
    | Data.Nat.Properties.+-comm  (length (proj₂ trace)) 1
    | pr1 =  refl
... | inj₂ pr2 rewrite
    (lemm2 snd (length (proj₂ trace)) (Eq.subst (WFCS snd) (Eq.sym pr) wfcs) (proj₂ trace ++ [ x %% modulus ] ))
    | take-all'' (proj₂ trace)  [ x %% modulus ]
    | pr2   = brr3 ((foldr (λ _ → suc) 0 (proj₂ trace ++ (x %% modulus) ∷ []) ≡ᵇ suc fst)) _  

completeness (add x₁ x₂) trace cs@(fst ,, snd) pos (p1 ,, p2 ,, p3 ,, p4) wfcs pr rp prop with satCS cs (proj₂ trace) ≟b true
completeness (add x₁ x₂) trace cs@(fst ,, snd) pos (p1 ,, p2 ,, p3 ,, p4) wfcs refl rp prop | .true because ofʸ a
   rewrite a
 |  mlength-++ (proj₂ trace) [ (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus ]
 | Data.Nat.Properties.+-comm  (length (proj₂ trace)) 1
 | and-lft (length (proj₂ trace) ≡ᵇ fst) _ a
 | aux7 snd (proj₂ trace) [  (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus ] (and-rgt _ _ a)
 |   aux8 fst ((lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus) (proj₂ trace) (aux10 _ _ (and-lft _ _ a))
 | lkpmb=lkpmb x₁ (proj₂ trace) [ (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus  ] p3
 | lkp=lkpmb x₁ (proj₂ trace) p3
 | lkpmb=lkpmb x₂ (proj₂ trace) [ (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus  ] p4
 | lkp=lkpmb x₂ (proj₂ trace) p4
 | modmod (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace))
 | aux9 ((lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus)
  =  prop

completeness (add x₁ x₂) trace cs@(fst ,, snd) pos (p1 ,, p2 ,, p3 ,, p4) wfcs refl rp prop
  | .false because ofⁿ a rewrite brr _ a | Eq.sym prop with brr2 _ (satCS' snd (proj₂ trace)) (brr _ a)
... | inj₁ pr1 rewrite mlength-++ (proj₂ trace) [ (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus ]
    | Data.Nat.Properties.+-comm  (length (proj₂ trace)) 1
    | pr1 = refl
... | inj₂ pr2 rewrite
    (lemm2 snd (length (proj₂ trace)) wfcs (proj₂ trace ++ (lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus ∷ []))
    | take-all'' (proj₂ trace) (((lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus) ∷ [])
    | pr2
      = brr3 ((foldr (λ _ → suc) 0
       (proj₂ trace ++ ((lkp x₁ (proj₂ trace) +ᵢ lkp x₂ (proj₂ trace)) %% modulus) ∷ [])
       ≡ᵇ suc fst)) _
       
completeness (seq c₁ c₂) trace cs pos wfc wfcs pr rp prop
 = completeness c₂
    (genTraceA c₁ trace)
    (genCS c₁ cs)
    (extInps c₁ (proj₁ pos ,, proj₂ pos))
    (proj₂ wfc)
    (Eq.subst (λ s → WFCS (proj₂ (genCS c₁ cs)) s) (aux c₁ cs pos (Eq.sym rp)) (lemm1 c₁ pos cs (proj₁ wfc) rp
        (Eq.subst (WFCS (proj₂ cs)) rp wfcs)))
    (Eq.sym ((extInps-genTraceA c₁ trace) pos (Eq.sym pr)))
    (Eq.sym (aux c₁ cs pos (Eq.sym rp)))
    (completeness c₁ trace cs pos (proj₁ wfc) wfcs pr rp prop)
    
completeness (mul x₁ x₂) trace cs pos wfc wfcs pr rp prop with satCS cs (proj₂ trace) ≟b true
... | .true because ofʸ a = {! !}
... | .false because ofⁿ a = {! !}


completeness _ = {!!}


soundness :  (c : Circuit)
  → (trace : List ℤ)
  → (pos : ℕ × List ℕ)
  → (cs : CS)
  → proj₁ pos ≡ proj₁ cs
  → WFCS (proj₂ cs) (proj₁ cs)
  → WellFormedCircuit c pos
  → satCS (genCS c cs) trace ≡ true
  → projPos (extInps c pos) (genTrace c (take (proj₁ cs) trace))
    ≡ projPos (extInps c pos) trace

soundness empty trace pos cs refl wfcs wfc pr rewrite Eq.sym (eqb-eq {length trace} {proj₁ cs} (and-lft ((length trace ≡ᵇ proj₁ cs)) _ pr))  | take-all' trace  = refl
soundness (add x x₁) trace pos cs refl wfcs (p1 ,, p2 ,, p3 ,, p4) pr = 
 Eq.cong (projPos (suc (proj₁ pos) ,, suc (proj₁ pos) ∷ proj₂ pos)) (Eq.trans (take-drop''  (take (proj₁ cs) trace) _ _ (Eq.trans (  Eq.cong (λ x → x  ∷ []) (o d)) ((Eq.sym (take-drop' trace (proj₁ cs) q))))) 
         (Eq.sym (take-drop trace  (proj₁ cs)))) 
  where
    exp = (mb2b
           (lkpmb x trace >>=m
              (λ xc →
                lkpmb x₁ trace >>=m
                  (λ yc →
                      lkpmb (proj₁ cs) trace >>=m
                         (λ zc → just (isYes ((xc +ᵢ yc) %% modulus ≟z zc)))))))

    q : (length trace ≡ suc (proj₁ cs))
    q = eqb-eq (and-lft _ _ pr)

    d : exp ≡ true
    d = and-lft _ _  (and-rgt (length trace ≡ᵇ suc (proj₁ cs)) _ pr)


    o : exp ≡ true →  (lkp x (take (proj₁ cs) trace) +ᵢ lkp x₁ (take (proj₁ cs) trace)) %% modulus
       ≡  (lkp (proj₁ cs) trace) 
    o  rewrite lkp=lkpmb (proj₁ cs) trace (eq-leq (Eq.sym q))
       | lkp=lkpmb x trace (Data.Nat.Properties.≤-trans p3 (Eq.subst (λ s → proj₁ cs ≤ s) (Eq.sym q) (Data.Nat.Properties.n≤1+n _)))
       | lkp=lkpmb x₁ trace (Data.Nat.Properties.≤-trans p4 (Eq.subst (λ s → proj₁ cs ≤ s) (Eq.sym q) (Data.Nat.Properties.n≤1+n _)))
       | Eq.sym (take-longer trace (proj₁ cs) x p3)
       | Eq.sym (take-longer trace (proj₁ cs) x₁ p4) = λ qq → (aux11 _ _ qq)

soundness (eq0 x) trace pos cs org wfcs p pr = o
  where
    q : (length trace ≡ (proj₁ cs))
    q = eqb-eq (and-lft (length trace ≡ᵇ proj₁ cs) _ pr)

    o : projPos pos (take (proj₁ cs) trace) ≡ projPos pos trace
    o rewrite Eq.sym q | take-all (length trace) trace Data.Nat.Properties.≤-refl = refl



soundness (const x) trace pos cs org wfcs p pr
   = Eq.cong (projPos (suc (proj₁ pos) ,, suc (proj₁ pos) ∷ proj₂ pos))
         (Eq.trans (take-drop''  (take (proj₁ cs) trace) _ _
                                  (Eq.trans (Eq.cong (λ x → x ∷ []) ( o d)) (Eq.sym ((take-drop' trace (proj₁ cs) q)))))
         (Eq.sym (take-drop trace  (proj₁ cs))))
         
  where
    q : (length trace ≡ suc (proj₁ cs))
    q = eqb-eq (and-lft _ _ pr)

    d : (mb2b (lkpmb (proj₁ cs) trace >>=m (λ xv → just (isYes (xv ≟z x %% modulus))))) ≡ true
    d =  and-lft _ _ (and-rgt (length trace ≡ᵇ suc (proj₁ cs)) _ pr) 

    o : (mb2b (lkpmb (proj₁ cs) trace >>=m (λ xv → just (isYes (xv ≟z x %% modulus))))) ≡ true → x %% modulus ≡ (lkp (proj₁ cs) trace) 
    o rewrite lkp=lkpmb (proj₁ cs) trace (eq-leq (Eq.sym q)) = λ qq → Eq.sym (aux11 _ _ qq)

soundness c@(seq c₁ c₂) trace pos cs org wfcs wfc prf
   =  Eq.trans (proj-cong  c₂ (extInps c₁ pos) (genTrace c₁ (take (proj₁ cs) trace)) (take (proj₁ (genCS c₁ cs)) trace) (proj₂ wfc) prf₁) prf₂'
  where
   prf-sat :  satCS' (proj₂ (genCS c₁ cs)) trace ≡ true
   prf-sat = aux5 c₂ (genCS c₁ cs) trace (and-rgt _ _ prf)


   prf₁' : projPos (extInps c₁ pos) (genTrace c₁
                         (take (proj₁ cs) (take (proj₁ (genCS c₁ cs)) trace)))
      ≡ projPos (extInps c₁ pos) (take (proj₁ (genCS c₁ cs)) trace)
   prf₁' = soundness c₁ (take (proj₁ (genCS c₁ cs)) trace) pos cs org wfcs (proj₁ wfc) ((and-int ((length
             (take (proj₁ (genCS c₁ cs)) trace)
                    ≡ᵇ proj₁ (genCS c₁ cs))) _ (aux4 (proj₁ (genCS c₁ cs)) trace
                 (leq-trans (aux3 c₂ (genCS c₁ cs)) (eq-leq (Eq.sym ((eqb-eq (and-lft _ _ prf)))))))
       (Eq.trans (Eq.sym (lemm2 (proj₂ (genCS c₁ cs)) (proj₁ (genCS c₁ cs)) (lemm1 c₁ pos cs (proj₁ wfc) org wfcs)  trace)) prf-sat )))

   q : (take (proj₁ cs) (take (proj₁ (genCS c₁ cs)) trace)) ≡ (take (proj₁ cs) trace)
   q = aux2 (aux3 c₁ _) _


   prf₁ : projPos (extInps c₁ pos)
                    (genTrace c₁ (take (proj₁ cs) trace))
      ≡ projPos (extInps c₁ pos) (take (proj₁ (genCS c₁ cs)) trace)
   prf₁ rewrite (Eq.sym q) = prf₁'


   s :   projPos (extInps c₂ (extInps c₁ pos))  (genTrace c₂ (genTrace c₁ (take (proj₁ cs) trace)))
           ≡ projPos (extInps c₂ (extInps c₁ pos))  (genTrace c₂ (take (proj₁ (genCS c₁ cs)) trace))
   s   = proj-cong c₂ (extInps c₁ pos) (genTrace c₁ (take (proj₁ cs) trace)) (take (proj₁ (genCS c₁ cs)) trace) (proj₂ wfc) prf₁


   prf₂' : projPos (extInps c₂ (extInps c₁ pos)) (genTrace c₂ (take (proj₁ (genCS c₁ cs)) trace)) ≡ projPos (extInps c₂ (extInps c₁ pos)) trace
   prf₂' = soundness c₂ trace ((extInps c₁ pos)) (genCS c₁ cs) (Eq.sym (aux c₁  cs pos (Eq.sym org))) (lemm1 c₁ pos cs (proj₁ wfc) org wfcs) (proj₂ wfc) prf
soundness _ = {!!}
