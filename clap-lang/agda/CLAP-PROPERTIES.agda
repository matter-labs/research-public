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
open import EGCD modulus




weakext : (c : Circuit) → (pos : ℕ × List ℕ) → proj₁ pos ≤ proj₁ (extInps c pos)
weakext empty pos = Data.Nat.Properties.≤-refl
weakext (const x) pos = Data.Nat.Properties.n≤1+n _
weakext (add x x₁) pos = Data.Nat.Properties.n≤1+n _
weakext (seq c₁ c₂) pos with weakext c₂ (extInps c₁ pos)
... | o = Data.Nat.Properties.≤-trans (weakext c₁ pos) o 
weakext (eq0 x) pos = Data.Nat.Properties.≤-refl

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


aux' : (c : Circuit) → (cs : CS) → (proj₁ cs) ≤  proj₁ (genCS c cs)
aux' empty cs = Data.Nat.Properties.≤-refl
aux' (const x) cs = Data.Nat.Properties.n≤1+n _
aux' (add x x₁) cs = Data.Nat.Properties.n≤1+n _
aux' (seq c₁ c₂) cs with aux' c₂ (genCS c₁ cs)
... | o = Data.Nat.Properties.≤-trans (aux' c₁ cs) o
aux' (eq0 x) cs = Data.Nat.Properties.≤-refl


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
--lemm1 _ = {!!}


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


and-lft : (a b : Bool) → a ∧ b ≡ true → a ≡ true
and-lft true true p = refl

and-rgt : (a b : Bool) → a ∧ b ≡ true → b ≡ true
and-rgt true true p = refl

and-int : (a b : Bool) → a ≡ true → b ≡ true → a ∧ b ≡ true
and-int true true p1 p2 = refl


eq-leq : {a b : ℕ} → a ≡ b → a ≤ b
eq-leq refl = Data.Nat.Properties.≤-refl

eqb-eq : {a b : ℕ} → (a ≡ᵇ b) ≡ true → a ≡ b
eqb-eq {zero} {zero} p = refl
eqb-eq {suc a} {suc b} p = Eq.cong suc (eqb-eq p)

eq-eqb : {a b : ℕ} → a ≡ b → (a ≡ᵇ b) ≡ true
eq-eqb {zero} {zero} p = refl
eq-eqb {suc a} {suc .a} refl = eq-eqb {a} {a} refl

mlength-++ : {A : Set} → (l1 l2 : List A) →  length (l1 ++ l2) ≡ length l1 + length l2
mlength-++ [] l2 = refl
mlength-++ (x ∷ l1) l2 = Eq.cong suc (mlength-++ l1 l2)

take-len : {A : Set} → (l : List A) → (n : ℕ) → (n ≤ length l) →  length (take n l) ≡ n
take-len [] .zero z≤n = refl
take-len (x ∷ l) zero p = refl
take-len (x ∷ l) (suc n) (s≤s p) = Eq.cong suc (take-len l n p)

aux5 : (c : Circuit) → (cs : CS) → (trace : List ℤ) →  satCS' (proj₂ (genCS c cs)) trace ≡ true
     → satCS' (proj₂ cs) trace ≡ true
aux5 empty cs trace p = p
aux5 (const x) cs trace p = and-rgt _ _ p
aux5 (add x x₁) cs trace p = and-rgt _ _ p
aux5 (seq c c₁) cs trace p = aux5 c _ trace (aux5 c₁ (genCS c cs) trace p)
aux5 (eq0 x) cs trace p = and-rgt _ _ p

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
--aux3 _ = {!!}

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
--extInps-genTrace _ = {!!}

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
--extInps-genTraceA _ = {!!}





projPos : List ℕ → List ℤ → List ℤ
projPos [] l = []
projPos (x ∷ n) l = lkp x l ∷ projPos n l


 
lkp-const : (trace : List ℤ) → (n : ℕ) → (x : ℤ) → length trace ≡ n
  → lkp n (genTrace (const x) trace) ≡ x %% modulus
lkp-const [] zero x p = refl
lkp-const (x₁ ∷ t) (suc n) x p = lkp-const t n x (Eq.cong Data.Nat.pred p) 


lkp-p : (n : ℕ) → (t : List ℤ) → (x : ℤ) → length t ≡ n → lkp n (t ++ [ x ]) ≡ x
lkp-p zero [] x pr = refl
lkp-p (suc n) (x₁ ∷ t) x pr = lkp-p n t x (Eq.cong Data.Nat.pred pr)

lkp-add : (trace : List ℤ) → (n a b : ℕ) → length trace ≡ n
  → lkp n (genTrace (add a b) trace) ≡ (lkp a trace +ᵢ lkp b trace) %% modulus
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
proj-lem x .(x ∷ _) t1 t2 (here refl) prf = Eq.cong (λ x → fromMaybe (ᵢ+ 0) (Data.List.head x)  ) prf
proj-lem x .(_ ∷ _) t1 t2 (there xin) prf = proj-lem x _  t1 t2  xin (Eq.cong (Data.List.drop 1) prf)

proj-cong : (c : Circuit) → (pos : ℕ × List ℕ) → (trace1 trace2 : List ℤ)
  → WellFormedCircuit c pos
  → projPos (proj₂ pos) trace1  ≡ projPos (proj₂ pos) trace2
  → length trace1 ≡ proj₁ pos
  → length trace2 ≡ proj₁ pos
  → projPos (proj₂ (extInps c pos)) (genTrace c trace1) ≡ projPos (proj₂ (extInps c pos)) (genTrace c trace2)
proj-cong empty pos trace1 trace2 wf hyp a b = hyp
proj-cong (const x) pos trace1 trace2 wf hyp a b rewrite lkp-const trace1  (proj₁ pos) x a
  | lkp-const trace2  (proj₁ pos) x b = Eq.cong ((λ l → x %% modulus ∷ l)) (ext-projPos  (proj₂ pos) trace1 trace2 _ (Eq.trans a (Eq.sym b)) hyp)
proj-cong (eq0 x) pos trace1 trace2 wf hyp a b = hyp
proj-cong (add x x₁) pos trace1 trace2 (wf1 ,, wf2) hyp a b
 rewrite lkp-add trace1 (proj₁ pos) x x₁ a
 | lkp-add trace2 (proj₁ pos) x x₁ b
 | proj-lem x (proj₂ pos) trace1 trace2  wf1 hyp
 | proj-lem x₁ (proj₂ pos) trace1 trace2  (proj₁ wf2) hyp
   =  Eq.cong (λ l →  _ ∷ l) (ext-projPos (proj₂ pos) trace1 trace2 _ (Eq.trans a (Eq.sym b)) hyp)
proj-cong (seq c c₁) pos trace1 trace2 wf hyp a b =
   proj-cong c₁  _ (genTrace c trace1) (genTrace c trace2) (proj₂ wf)
                   (proj-cong c pos trace1 trace2  (proj₁ wf) hyp  a b) (Eq.sym (extInps-genTrace c trace1 pos (Eq.sym a))) (Eq.sym (extInps-genTrace c trace2 pos (Eq.sym b)))



Complete : Circuit → Set
Complete c = (trace : Bool × List ℤ)
  → (cs : CS)
  → (pos : ℕ × List ℕ)
  → WellFormedCircuit c pos
  → WFCS (proj₂ cs) (proj₁ pos)
  → length (proj₂ trace) ≡ proj₁ pos
  → (proj₁ pos) ≡ proj₁ cs
  → satCS cs (proj₂ trace) ≡ (proj₁ trace)
  → satCS (genCS c cs) (proj₂ (genTraceA c trace)) ≡ proj₁ (genTraceA c trace)


PosCorrect : ℕ × List ℕ → Set
PosCorrect pos = (x : ℕ) → x ∈ proj₂ pos → suc x ≤ proj₁ pos

pos-corr : (pos : ℕ × List ℕ) → (c : Circuit) → WellFormedCircuit c pos
  → PosCorrect pos → PosCorrect (extInps c pos)
pos-corr pos empty wf pc x y = pc x y
pos-corr pos (const x₁) tt pc .(proj₁ pos) (here refl) = Data.Nat.Properties.≤-refl
pos-corr pos (const x₁) tt pc x (there px) = Data.Nat.Properties.m≤n⇒m≤1+n (pc x px)
pos-corr pos (add x₁ x₂) wf pc .(proj₁ pos) (here refl) = Data.Nat.Properties.≤-refl
pos-corr pos (add x₁ x₂) wf pc x (there y) = Data.Nat.Properties.m≤n⇒m≤1+n (pc x y)
pos-corr pos (eq0 x₁) wf pc x y = pc x y
pos-corr pos (seq c c₁) wf pc  = pos-corr _ c₁ (proj₂ wf) (pos-corr pos c (proj₁ wf) pc) 

Sound : Circuit → Set
Sound c =  (trace : List ℤ)
  → (pos : ℕ × List ℕ)
  → (∀ x → x ∈ proj₂ pos → suc x ≤ proj₁ pos)
  → (cs : CS)
  → proj₁ pos ≡ proj₁ cs
  → WFCS (proj₂ cs) (proj₁ cs)
  → WellFormedCircuit c pos
  → satCS (genCS c cs) trace ≡ true
  → projPos (proj₂ (extInps c pos)) (genTrace c (take (proj₁ cs) trace))
    ≡ projPos (proj₂ (extInps c pos)) trace
    × satCS (genCS c cs) (genTrace c (take (proj₁ cs) trace)) ≡ true


Soundness : Circuit → Set
Soundness c = (cs : CS) → (pos : ℕ × List ℕ) → (trace1 trace2 : List ℤ)
  → PosCorrect pos
  → proj₁ cs ≡ proj₁ pos
  → WFCS (proj₂ cs) (proj₁ cs)
  → length trace1 ≡ proj₁ (genCS c cs)
  → length trace2 ≡ proj₁ cs
  → WellFormedCircuit c pos  
  → satCS (genCS c cs) trace1 ≡ true
  → satCS cs trace2 ≡ true  
  → projPos (proj₂ pos) trace1 ≡ projPos (proj₂ pos) trace2
  → satCS (genCS c cs) (genTrace c trace2) ≡ true
   × projPos (proj₂ (extInps c pos)) trace1 
     ≡ projPos (proj₂ (extInps c pos)) (genTrace c trace2)


completenessComp :  (c₁ c₂ : Circuit)
 → Complete c₁ 
 → Complete c₂
 → Complete (seq c₁ c₂)
completenessComp c₁ c₂ cmplt1 cmplt2 trace cs pos wfc wfcs pr rp prop 
 = cmplt2 
    (genTraceA c₁ trace)
    (genCS c₁ cs)
    (extInps c₁ (proj₁ pos ,, proj₂ pos))
    (proj₂ wfc)
    (Eq.subst (λ s → WFCS (proj₂ (genCS c₁ cs)) s) (aux c₁ cs pos (Eq.sym rp)) (lemm1 c₁ pos cs (proj₁ wfc) rp
        (Eq.subst (WFCS (proj₂ cs)) rp wfcs)))
    (Eq.sym ((extInps-genTraceA c₁ trace) pos (Eq.sym pr)))
    (Eq.sym (aux c₁ cs pos (Eq.sym rp)))
    (cmplt1 trace cs pos (proj₁ wfc) wfcs pr rp prop)


lkp-take : (x fst : ℕ) → (trace : List ℤ) → suc x ≤ fst → lkp x trace ≡ lkp x (take fst trace)
lkp-take x .(suc _) [] (s≤s eqx) = refl
lkp-take zero .(suc _) (x₁ ∷ trace) (s≤s eqx) = refl
lkp-take (suc x) .(suc _) (x₁ ∷ trace) (s≤s eqx) = lkp-take x _ trace eqx


projPos-cor : (pos : ℕ × List ℕ) → (trace : List ℤ)
  → ((x : ℕ) → x ∈ proj₂ pos → suc x ≤ proj₁ pos)
  → projPos (proj₂ pos) trace ≡
      projPos (proj₂ pos) (take (proj₁ pos) trace)
projPos-cor (fst ,, []) trace prop = refl
projPos-cor (fst ,, x ∷ snd) trace prop rewrite (projPos-cor (fst ,, snd) trace λ x xp → prop x (there xp))
 | lkp-take x fst trace (prop x (here _) )
  = refl


projPos-cor2 : (n : ℕ) → (pos : ℕ × List ℕ) → (trace : List ℤ)
  → PosCorrect pos
  → proj₁ pos ≤ n
  → projPos (proj₂ pos) trace ≡
      projPos (proj₂ pos) (take n trace)
projPos-cor2 n (fst ,, []) trace prop p = refl
projPos-cor2 n (fst ,, x ∷ snd) trace prop1 prop2
 rewrite projPos-cor2 n (fst ,, snd) trace (λ x y → prop1 x (there y)) prop2 
 | lkp-take x n trace (Data.Nat.Properties.≤-trans (prop1 x (here refl)) prop2)
  = refl


soundness-composable : (c₁ c₂ : Circuit)
  → Soundness c₁
  → Soundness c₂
  → Soundness (seq c₁ c₂)
soundness-composable c c₁ hyp1 hyp2 cs pos t1 t2  posCorr cspos w1 l1 l2 wfc sat1 sat2 pr1
  = hyp2 (genCS c cs) 
         (extInps c pos) t1 
         (genTrace c t2) --c₁
         (pos-corr pos c (proj₁ wfc)  posCorr)
         (aux c cs pos cspos)
         (lemm1 c pos cs (proj₁ wfc) (Eq.sym zz) w1) l1
         (Eq.sym (Eq.trans (aux c cs pos zz) 
                     (extInps-genTrace c t2 pos (Eq.trans (Eq.sym zz) (Eq.sym l2))))) 
               (proj₂ wfc) sat1 (proj₁ qq) 
              qq2 
    where
     kk : PosCorrect pos
     kk = posCorr

     zz : proj₁ cs ≡ proj₁ pos
     zz = cspos

     ii : (length (take (proj₁ (genCS c cs)) t1) ≡ proj₁ (genCS c cs))
     ii =  (take-len _ _ (Data.Nat.Properties.≤-trans (aux' c₁ (genCS c cs)) (eq-leq (Eq.sym l1))))

     pp : satCS (genCS c cs) (take (proj₁ (genCS c cs)) t1) ≡ true
     pp = and-int (length (take (proj₁ (genCS c cs)) t1) ≡ᵇ proj₁ (genCS c cs)) 
          _ (eq-eqb ii) 
         (Eq.trans (Eq.sym ((lemm2 (proj₂ (genCS c cs)) (proj₁ (genCS c cs)) (lemm1 c pos cs (proj₁ wfc) (Eq.sym zz) w1) t1))) 
         (aux5 c₁ (genCS c cs) t1 (and-rgt _ _ sat1)))

     qq' : projPos (proj₂ pos) (take (proj₁ (genCS c cs)) t1) ≡
      projPos (proj₂ pos) t1
     qq' rewrite (aux c cs pos zz)  = Eq.sym (projPos-cor2 (proj₁ (extInps c pos)) pos t1 kk (weakext c pos))
     
     qq : (satCS ((genCS c cs)) (genTrace c t2) ≡ true) 
            × projPos (proj₂ (extInps c pos)) (take (proj₁ (genCS c cs)) t1) ≡
              projPos (proj₂ (extInps c pos)) (genTrace c t2)
     qq = hyp1 cs pos (take (proj₁ (genCS c cs)) t1) t2  posCorr cspos w1 (take-len _ _ (Data.Nat.Properties.≤-trans 
            (aux' c₁ (genCS c cs)) (eq-leq (Eq.sym l1)))) l2 (proj₁ wfc) pp  sat2 (Eq.trans qq' pr1)

     qq2 : projPos (proj₂ (extInps c pos)) t1 ≡
      projPos (proj₂ (extInps c pos)) (genTrace c t2)
     qq2 rewrite (Eq.sym (proj₂ qq))
      | (aux c cs pos zz) = projPos-cor (extInps c pos) t1 (pos-corr pos c (proj₁ wfc) kk)

