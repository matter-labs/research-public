
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_ ; _≤?_; z≤n; s≤s; _+_; _*_ ; _≟_ ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.List renaming (map to mapₗ ; find to findₗ ; zip to zipₗ ; concat to concatₗ) hiding (fromMaybe)
open import Data.Bool hiding (_≤_ ; _≤?_) renaming (_≟_ to _≟b_)
open import Data.Integer renaming (_*_ to _*ᵢ_ ; _≟_ to _≟z_ ; +_ to ᵢ+_)
  using (_≤ᵇ_ ; ℤ ; -[1+_] ; _/_ ; ≢-nonZero ; _%_ ; _-_ ; ∣_∣ )
  
module CLAP-PROPERTIES (Field : Set) (zeroF :  Field) (Gate : Set)(Expr : Set) 
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

open import Data.Maybe renaming (_>>=_ to _>>=m_)
open import Data.Sum hiding ([_,_])

open import Data.Nat.Properties using (≤-totalOrder)
open import Data.List.Extrema ≤-totalOrder

open import Relation.Nullary
open import CLAP-BASE Field zeroF Gate Expr extInps-gate  WellFormedGate genTraceGate genTraceAGate genCS-gate WFCS-expr satCS'-expr 




module SoundnessAndCompletenessCompose 
  (extInpsMonotonic-gate : (c : Gate) 
    → (pos : ℕ × List ℕ) 
    → proj₁ pos ≤ proj₁ (extInps-gate c pos)) 
  (genCSMonotonic-gate : (c : Gate) 
    → (cs : CS)  
    → proj₁ cs ≤ proj₁ (genCS-gate c cs))
  (genCS-extInps-agree-gate : (c : Gate) 
   → (cs : CS) 
   → (pos : ℕ × List ℕ)  
   → proj₁ cs ≡ proj₁ pos 
   → proj₁ (genCS-gate c cs)
       ≡ proj₁ (extInps-gate c pos))   
  (genCS-WFCS-gate : (c : Gate) 
   → (pos : ℕ × List ℕ) 
   → (cs : CS)
   → WellFormedGate c pos
   → proj₁ pos ≡ proj₁ cs
   → WFCS (proj₂ cs) (proj₁ cs)
   → WFCS (proj₂ (genCS-gate c cs)) (proj₁ (genCS-gate c cs)))
  (satCS'-weaken-gate : (c : Gate) → (cs : CS) → (trace : List Field) 
   → satCS' (proj₂ (genCS-gate c cs)) trace ≡ true
   → satCS' (proj₂ cs) trace ≡ true)
  (extInps-genTrace-gate : (c : Gate) 
   → (trace : List Field) 
   → (pos : ℕ × List ℕ) 
   → proj₁ pos ≡ length trace
   → proj₁ (extInps-gate c pos) ≡ (length (genTraceGate c trace)))
  (extInps-genTraceA-gate : (c : Gate) 
    → (trace : Bool × List Field) 
    → (pos : ℕ × List ℕ)
    → proj₁ pos ≡ length (proj₂ trace)
    → proj₁ (extInps-gate c pos) ≡ (length (proj₂ (genTraceAGate c trace))))
  (proj-cong-gate : (c : Gate) 
    → (pos : ℕ × List ℕ) 
    → (trace1 trace2 : List Field)
    → WellFormedGate c pos
    → projPos (proj₂ pos) trace1  ≡ projPos (proj₂ pos) trace2
    → length trace1 ≡ proj₁ pos
    → length trace2 ≡ proj₁ pos
    → projPos (proj₂ (extInps-gate c pos)) (genTraceGate c trace1) 
        ≡ projPos (proj₂ (extInps-gate c pos)) (genTraceGate c trace2))
  (posCorr-extInps-gate : (c : Gate)
    → (pos : ℕ × List ℕ) 
    → WellFormedGate c pos
    → PosCorrect pos 
    → PosCorrect (extInps-gate c pos))
  (genCS-WFCS-weak-expr : (n : ℕ) →  (cs : Expr) → WFCS-expr cs n → WFCS-expr cs (suc n))
  (lemm2-expr : (exprs : Expr)(n : ℕ) → WFCS-expr exprs n → (trace : List Field)
    → satCS'-expr exprs trace ≡ satCS'-expr exprs (take n trace))
 where


 Completeness : Circuit → Set
 Completeness c = (trace : Bool × List Field)
   → (cs : CS)
   → (pos : ℕ × List ℕ)
   → WellFormedCircuit c pos
   → WFCS (proj₂ cs) (proj₁ pos)
   → length (proj₂ trace) ≡ proj₁ pos
   → (proj₁ pos) ≡ proj₁ cs
   → satCS cs (proj₂ trace) ≡ (proj₁ trace)
   → satCS (genCS c cs) (proj₂ (genTraceA c trace)) ≡ proj₁ (genTraceA c trace)


 Soundness : Circuit → Set
 Soundness c = (cs : CS) → (pos : ℕ × List ℕ) → (trace1 trace2 : List Field)
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
       × (projPos (proj₂ (extInps c pos)) trace1 
          ≡ projPos (proj₂ (extInps c pos)) ((genTrace c trace2)))


 extInpsMonotonic : (c : Circuit) → (pos : ℕ × List ℕ) → proj₁ pos ≤ proj₁ (extInps c pos)
 extInpsMonotonic empty pos = Data.Nat.Properties.≤-refl
 extInpsMonotonic (seq c₁ c₂) pos with extInpsMonotonic c₂ (extInps c₁ pos)
 ... | o = Data.Nat.Properties.≤-trans (extInpsMonotonic c₁ pos) o 
 extInpsMonotonic (par c₁ c₂) pos with extInpsMonotonic c₂ (extInps c₁ pos)
 ... | o = Data.Nat.Properties.≤-trans (extInpsMonotonic c₁ pos) o 
 extInpsMonotonic (gate x) pos = extInpsMonotonic-gate x pos


 genCS-extInps-agree : (c : Circuit) → (cs : CS) → (pos : ℕ × List ℕ) 
   → proj₁ cs ≡ proj₁ pos
   → (proj₁ (genCS c cs)) ≡  proj₁ (extInps c pos)
 genCS-extInps-agree empty pr pos pp = pp
 genCS-extInps-agree (gate x) pr pos refl = genCS-extInps-agree-gate x pr pos refl 
 genCS-extInps-agree (seq c c₁) (.(proj₁ pos) ,, snd) pos refl 
  = genCS-extInps-agree c₁ _ _ (genCS-extInps-agree c _ pos refl)
 genCS-extInps-agree (par c c₁) (.(proj₁ pos) ,, snd) pos refl 
  = genCS-extInps-agree c₁ _ _ (genCS-extInps-agree c _ pos refl)
  

 aux' : (c : Circuit) → (cs : CS) → (proj₁ cs) ≤  proj₁ (genCS c cs)
 aux' empty cs = Data.Nat.Properties.≤-refl
 aux' (gate x) cs = genCSMonotonic-gate x cs
 aux' (seq c₁ c₂) cs with aux' c₂ (genCS c₁ cs)
 ... | o = Data.Nat.Properties.≤-trans (aux' c₁ cs) o
 aux' (par c₁ c₂) cs with aux' c₂ (genCS c₁ cs)
 ... | o = Data.Nat.Properties.≤-trans (aux' c₁ cs) o


 genCS-WFCS : (c : Circuit) → (pos : ℕ × List ℕ) → (cs : CS)
    → WellFormedCircuit c pos
    → proj₁ pos ≡ proj₁ cs
    → WFCS (proj₂ cs) (proj₁ cs)
    → WFCS (proj₂ (genCS c cs)) (proj₁ (genCS c cs))
 genCS-WFCS empty pos cs wfc wfcs pr = pr
 genCS-WFCS (gate x) pos cs wfc refl pr =  genCS-WFCS-gate x pos cs wfc refl pr 
 genCS-WFCS (seq c c₁) pos@(.(proj₁ cs) ,, snd) cs wfc refl wfcs 
   = genCS-WFCS c₁ _  (genCS c cs) (proj₂ wfc) 
      (Eq.sym (genCS-extInps-agree c  cs pos refl)) 
      (genCS-WFCS c pos cs (proj₁ wfc) refl wfcs)
 genCS-WFCS (par c c₁) pos@(.(proj₁ cs) ,, snd) cs wfc refl wfcs 
   = genCS-WFCS c₁ _  (genCS c cs) (proj₂ (proj₂ wfc)) 
      (Eq.sym (genCS-extInps-agree c  cs pos refl)) 
      (genCS-WFCS c pos cs (proj₁ wfc) refl wfcs)

 open import Extra

 lemm2 : (exprs : List Expr)(n : ℕ) → WFCS exprs n → (trace : List Field)
   → satCS' exprs trace ≡ satCS' exprs (take n trace)
 lemm2 [] n wf trace = refl
 lemm2 (e ∷ exprs) n wfcs trace rewrite lemm2 exprs n  (proj₂ wfcs) trace rewrite lemm2-expr e n (proj₁ wfcs) trace   = refl 
 
 eq-leq : {a b : ℕ} → a ≡ b → a ≤ b
 eq-leq refl = Data.Nat.Properties.≤-refl

 eqb-eq : {a b : ℕ} → (a ≡ᵇ b) ≡ true → a ≡ b
 eqb-eq {zero} {zero} p = refl
 eqb-eq {suc a} {suc b} p = Eq.cong suc (eqb-eq p)

 eq-eqb : {a b : ℕ} → a ≡ b → (a ≡ᵇ b) ≡ true
 eq-eqb {zero} {zero} p = refl
 eq-eqb {suc a} {suc .a} refl = eq-eqb {a} {a} refl

 take-len : {A : Set} → (l : List A) → (n : ℕ) → (n ≤ length l) →  length (take n l) ≡ n
 take-len [] .zero z≤n = refl
 take-len (x ∷ l) zero p = refl
 take-len (x ∷ l) (suc n) (s≤s p) = Eq.cong suc (take-len l n p)

 satCS'-weaken : (c : Circuit) → (cs : CS) → (trace : List Field) →  satCS' (proj₂ (genCS c cs)) trace ≡ true
      → satCS' (proj₂ cs) trace ≡ true
 satCS'-weaken empty cs trace p = p
 satCS'-weaken (gate x) cs trace p = satCS'-weaken-gate x cs trace p
 satCS'-weaken (seq c c₁) cs trace p = satCS'-weaken c _ trace (satCS'-weaken c₁ (genCS c cs) trace p)
 satCS'-weaken (par c c₁) cs trace p = satCS'-weaken c _ trace (satCS'-weaken c₁ (genCS c cs) trace p)


 genCSMonotonic : (c : Circuit) → (cs : CS) → (proj₁ cs) ≤ (proj₁ (genCS c cs))
 genCSMonotonic empty cs = Data.Nat.Properties.≤-refl
 genCSMonotonic (gate x) cs = genCSMonotonic-gate x cs
 genCSMonotonic (seq c c₁) cs with genCSMonotonic c cs | genCSMonotonic c₁ (genCS c cs)
 ... | p₁ | p₂ = Data.Nat.Properties.≤-trans p₁ p₂
 genCSMonotonic (par c c₁) cs with genCSMonotonic c cs | genCSMonotonic c₁ (genCS c cs)
 ... | p₁ | p₂ = Data.Nat.Properties.≤-trans p₁ p₂


 extInps-genTrace : (c : Circuit) → (trace : List Field) → (pos : ℕ × List ℕ) → proj₁ pos ≡ length trace
                      → proj₁ (extInps c pos) ≡ (length (genTrace c trace))
 extInps-genTrace (gate x) trace pos pr = extInps-genTrace-gate x trace pos pr
 extInps-genTrace empty trace pos pr = pr
 extInps-genTrace (seq c c₁) trace pos pr = extInps-genTrace c₁ (genTrace c trace) _ (extInps-genTrace c trace pos pr)
 extInps-genTrace (par c c₁) trace pos pr = extInps-genTrace c₁ (genTrace c trace) _ (extInps-genTrace c trace pos pr)

 extInps-genTraceA : (c : Circuit) → (trace : Bool × List Field) → (pos : ℕ × List ℕ)
    → proj₁ pos ≡ length (proj₂ trace)
    → proj₁ (extInps c pos) ≡ (length (proj₂ (genTraceA c trace)))
 extInps-genTraceA (gate x) trace pos pr = extInps-genTraceA-gate x trace pos pr 
 extInps-genTraceA empty trace pos pr = pr
 extInps-genTraceA (seq c c₁) trace pos pr = extInps-genTraceA c₁ (genTraceA c trace) _ (extInps-genTraceA c trace pos pr)
 extInps-genTraceA (par c c₁) trace pos pr = extInps-genTraceA c₁ (genTraceA c trace) _ (extInps-genTraceA c trace pos pr)


 ext-lkp : (trace1 trace2 ext : List Field) → (x : ℕ)
   → length trace1 ≡ length trace2
   → lkp x trace1 ≡ lkp x trace2
   → lkp x (trace1 ++ ext) ≡ lkp x (trace2 ++ ext)
 ext-lkp  [] [] ext x p1 p2 = refl
 ext-lkp (x₁ ∷ trace1) (x₂ ∷ trace2) ext zero p1 p2 = p2
 ext-lkp (x₁ ∷ trace1) (x₂ ∷ trace2) ext (suc x) p1 p2 = ext-lkp trace1 trace2 ext x (Eq.cong Data.Nat.pred p1) p2


 ext-projPos : (outs : List ℕ) → (trace1 trace2 ext : List Field)
   → length trace1 ≡ length trace2
   → projPos outs trace1 ≡ projPos outs trace2
   → projPos outs (trace1 ++ ext) ≡ projPos outs (trace2 ++ ext)
 ext-projPos [] (trace1) (trace2) ext prf eq = refl
 ext-projPos (x₂ ∷ outs) (trace1) (trace2) ext prf eq 
  rewrite ext-projPos outs trace1 trace2 ext prf 
          (Eq.cong (Data.List.drop 1) eq) 
  = Eq.cong (λ x → x ∷ projPos outs (trace2 ++ ext)) q
   where
      w : lkp x₂ trace1 ≡ lkp x₂ trace2
      w = Eq.cong (λ x → fromMaybe zeroF (Data.List.head x)  )  eq

      q : lkp x₂ (trace1 ++ ext) ≡ lkp x₂ (trace2 ++ ext)
      q = ext-lkp trace1 trace2 ext  x₂ prf w


 proj-cong : (c : Circuit) → (pos : ℕ × List ℕ) → (trace1 trace2 : List Field)
   → WellFormedCircuit c pos
   → projPos (proj₂ pos) trace1  ≡ projPos (proj₂ pos) trace2
   → length trace1 ≡ proj₁ pos
   → length trace2 ≡ proj₁ pos
   → projPos (proj₂ (extInps c pos)) (genTrace c trace1) ≡ projPos (proj₂ (extInps c pos)) (genTrace c trace2)
 proj-cong empty pos trace1 trace2 wf hyp a b = hyp
 proj-cong (gate x) pos trace1 trace2 wf hyp a b = proj-cong-gate x pos trace1 trace2 wf hyp a b
 proj-cong (seq c c₁) pos trace1 trace2 wf hyp a b =
    proj-cong c₁  _ (genTrace c trace1) (genTrace c trace2) (proj₂ wf)
                    (proj-cong c pos trace1 trace2  (proj₁ wf) hyp  a b) 
                    (Eq.sym (extInps-genTrace c trace1 pos (Eq.sym a))) 
                    (Eq.sym (extInps-genTrace c trace2 pos (Eq.sym b)))
 proj-cong (par c c₁) pos trace1 trace2 wf hyp a b =
    proj-cong c₁  _ (genTrace c trace1) (genTrace c trace2) (proj₂ (proj₂ wf))
                    (proj-cong c pos trace1 trace2  (proj₁ wf) hyp  a b) 
                    (Eq.sym (extInps-genTrace c trace1 pos (Eq.sym a))) 
                    (Eq.sym (extInps-genTrace c trace2 pos (Eq.sym b)))


 posCorr-extInps : (pos : ℕ × List ℕ) → (c : Circuit) → WellFormedCircuit c pos
   → PosCorrect pos → PosCorrect (extInps c pos)
 posCorr-extInps pos empty wf pc x y = pc x y
 posCorr-extInps pos (gate x₁) wf pc x y = posCorr-extInps-gate x₁ pos wf pc x y
 posCorr-extInps pos (seq c c₁) wf pc  = posCorr-extInps _ c₁ (proj₂ wf) 
                                           (posCorr-extInps pos c (proj₁ wf) pc) 
 posCorr-extInps pos (par c c₁) wf pc  = posCorr-extInps _ c₁ (proj₂ (proj₂ wf)) 
                                           (posCorr-extInps pos c (proj₁ wf) pc) 


 completeness-composable :  (c₁ c₂ : Circuit)
  → Completeness c₁ 
  → Completeness c₂
  → Completeness (seq c₁ c₂)
 completeness-composable c₁ c₂ cmplt1 cmplt2 trace cs pos wfc wfcs pr rp prop 
  = cmplt2 
     (genTraceA c₁ trace)
     (genCS c₁ cs)
     (extInps c₁ (proj₁ pos ,, proj₂ pos))
     (proj₂ wfc)
     (Eq.subst (λ s → WFCS (proj₂ (genCS c₁ cs)) s) (genCS-extInps-agree c₁ cs pos (Eq.sym rp)) 
         (genCS-WFCS c₁ pos cs (proj₁ wfc) rp
         (Eq.subst (WFCS (proj₂ cs)) rp wfcs)))
     (Eq.sym ((extInps-genTraceA c₁ trace) pos (Eq.sym pr)))
     (Eq.sym (genCS-extInps-agree c₁ cs pos (Eq.sym rp)))
     (cmplt1 trace cs pos (proj₁ wfc) wfcs pr rp prop)


 lkp-take : (x fst : ℕ) → (trace : List Field) → suc x ≤ fst → lkp x trace ≡ lkp x (take fst trace)
 lkp-take x .(suc _) [] (s≤s eqx) = refl
 lkp-take zero .(suc _) (x₁ ∷ trace) (s≤s eqx) = refl
 lkp-take (suc x) .(suc _) (x₁ ∷ trace) (s≤s eqx) = lkp-take x _ trace eqx


 projPos-cor : (pos : ℕ × List ℕ) → (trace : List Field)
   → ((x : ℕ) → x ∈ proj₂ pos → suc x ≤ proj₁ pos)
   → projPos (proj₂ pos) trace ≡
       projPos (proj₂ pos) (take (proj₁ pos) trace)
 projPos-cor (fst ,, []) trace prop = refl
 projPos-cor (fst ,, x ∷ snd) trace prop rewrite (projPos-cor (fst ,, snd) trace λ x xp → prop x (there xp))
  | lkp-take x fst trace (prop x (here refl) )
   = refl


 projPos-cor2 : (n : ℕ) → (pos : ℕ × List ℕ) → (trace : List Field)
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
          (posCorr-extInps pos c (proj₁ wfc)  posCorr)
          (genCS-extInps-agree c cs pos cspos)
          (genCS-WFCS c pos cs (proj₁ wfc) (Eq.sym cspos) w1) l1
          (Eq.sym (Eq.trans (genCS-extInps-agree c cs pos cspos) 
                      (extInps-genTrace c t2 pos (Eq.trans (Eq.sym cspos) (Eq.sym l2))))) 
                (proj₂ wfc) sat1 (proj₁ qq) 
               qq2 
     where

      ii : (length (take (proj₁ (genCS c cs)) t1) ≡ proj₁ (genCS c cs))
      ii =  (take-len _ _ (Data.Nat.Properties.≤-trans (aux' c₁ (genCS c cs)) (eq-leq (Eq.sym l1))))

      pp : satCS (genCS c cs) (take (proj₁ (genCS c cs)) t1) ≡ true
      pp = and-int (length (take (proj₁ (genCS c cs)) t1) ≡ᵇ proj₁ (genCS c cs)) 
           _ (eq-eqb ii) 
          (Eq.trans (Eq.sym ((lemm2 (proj₂ (genCS c cs)) (proj₁ (genCS c cs)) (genCS-WFCS c pos cs (proj₁ wfc) (Eq.sym cspos) w1) t1))) 
          (satCS'-weaken c₁ (genCS c cs) t1 (and-rgt _ _ sat1)))

      qq' : projPos (proj₂ pos) (take (proj₁ (genCS c cs)) t1) ≡
       projPos (proj₂ pos) t1
      qq' rewrite (genCS-extInps-agree c cs pos cspos)  = Eq.sym (projPos-cor2 (proj₁ (extInps c pos)) pos t1 posCorr (extInpsMonotonic c pos))

      qq : (satCS ((genCS c cs)) (genTrace c t2) ≡ true) 
             × projPos (proj₂ (extInps c pos)) (take (proj₁ (genCS c cs)) t1) ≡
               projPos (proj₂ (extInps c pos)) (genTrace c t2)
      qq = hyp1 cs pos (take (proj₁ (genCS c cs)) t1) t2  posCorr cspos w1 (take-len _ _ (Data.Nat.Properties.≤-trans 
             (aux' c₁ (genCS c cs)) (eq-leq (Eq.sym l1)))) l2 (proj₁ wfc) pp  sat2 (Eq.trans qq' pr1)

      qq2 : projPos (proj₂ (extInps c pos)) t1 ≡
       projPos (proj₂ (extInps c pos)) (genTrace c t2)
      qq2 rewrite (Eq.sym (proj₂ qq))
       | (genCS-extInps-agree c cs pos cspos) = projPos-cor (extInps c pos) t1 (posCorr-extInps pos c (proj₁ wfc) posCorr)



