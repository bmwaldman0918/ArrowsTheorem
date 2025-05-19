{-# OPTIONS --rewriting #-}
module Arrow where

open import Util.Voter
open WeakPreference
open StrictPreference
open Preference

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Util.Votes 
open import Util.Election
open SWF
open AlteredVoters

open import Util.Coalition
open import Util.Decisive
open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Vec
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Nat.Properties using (suc-injective)
open import Data.Vec.Properties using (∷-injectiveʳ)

private
  variable
    n : ℕ
    result : {m : ℕ} → Votes n m → Fin n → Fin n → Set

-- The coalition of the whole is decisive.
WholeIsDecisive : {m : ℕ} 
         → (v : Votes n m) 
         → (SWF result)
         → Decisive (Whole m) v result
WholeIsDecisive {m = m} v swf a b ca = Pareto swf v a b (helper m v a b ca) where
  helper : (m : ℕ) 
         → (v : Votes n m) 
         → (a b : Fin n) 
         → CoalitionAgrees a b (Whole m) v 
         → ElectionAgrees v a b
  helper .0 [] a b c = tt
  helper (suc m) (x ∷ v) a b (true-agrees .(Whole m) .v c .x agrees) = 
    agrees , (helper m v a b c)

-- A proof that a coalition is decisive for candidate over themselves is impossible.
Decisive-x>x : {m : ℕ}
             → (v : Votes n m) 
             → (c : NonEmptyCoalition m)
             → (a b : Fin n)
             → (a ≡ b)
             → (CoalitionAgrees a b (Unwrap c) v)
             → ⊥
Decisive-x>x v c a b a≡b ca = ⊥-elim (helper v c a b a≡b ca)
  where
    helper : {m n : ℕ} 
           → (v : Votes n m) 
           → (c : NonEmptyCoalition m) 
           → (a b : Fin n) 
           → (a ≡ b) 
           → (CoalitionAgrees a b (Unwrap c) v)
           → ⊥
    helper (p ∷ v) (.true ∷ c , _) a b a≡b 
      (true-agrees .c .v ca .p aPb) = ⊥-elim (aPb (R-refl p b a (Eq.sym a≡b)))
    helper (p ∷ v) (.(false ∷ c) , fst) a b a≡b 
      (false-agrees c .v ca .p) = helper v (c , fst) a b a≡b ca

-- Utility function to produce an arbitrary third candidate.
FreshCandidate : (n : ℕ) 
               → (n>2 : n ℕ.> 2) 
               → (a b : Fin n) 
               → Σ (Fin n) λ c → ¬ (a ≡ c) × ¬ (b ≡ c)
FreshCandidate (suc zero) (s≤s ()) a b
FreshCandidate (suc (suc zero)) (s≤s (s≤s ())) a b
FreshCandidate (suc (suc (suc n))) n>2 zero zero 
  = (suc zero) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 zero (suc zero) 
  = (suc (suc zero)) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 zero (suc (suc b)) 
  = (suc zero) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc zero) zero 
  = (suc (suc zero)) , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc a) (suc b) 
  = zero , ((λ {()}) , (λ {()}))
FreshCandidate (suc (suc (suc n))) n>2 (suc (suc a)) zero 
  = (suc zero) , ((λ {()}) , (λ {()}))

WeaklyDecisive-x>yImpliesDecisive-x>zSimilar : {m : ℕ}
                → (c : Coalition m) 
                → (v : Votes n m) 
                → (x y z : Fin n)
                → ¬ (x ≡ z) 
                → ¬ (y ≡ z)
                → ¬ (x ≡ y)
                → (CoalitionAgrees x z c v)
                → Σ (Votes n m) 
                  λ v' → ((CoalitionAgrees x y c v') 
                       ×  (CoalitionAgrees y x (InverseCoalition c) v')
                       ×  (ElectionAgrees v' y z)
                       ×  (Similar m x z (Zipped x z v v')))
WeaklyDecisive-x>yImpliesDecisive-x>zSimilar [] [] x y z ¬x≡z ¬y≡z ¬x≡y ca-x>z = 
  [] , (empty-coalition-agrees , empty-coalition-agrees , tt , tt)
WeaklyDecisive-x>yImpliesDecisive-x>zSimilar (c ∷ c-rem) (p ∷ v) x y z ¬x≡z ¬y≡z ¬x≡y
  (true-agrees .c-rem .v ca-x>z .p xPz)
  with WeaklyDecisive-x>yImpliesDecisive-x>zSimilar c-rem v x y z ¬x≡z ¬y≡z ¬x≡y ca-x>z
... | v' , c'-x>y , inv'-y>x , ea-y>z , sim-x-z
  with Alter-First p y -- x>y>z
... | R' , p' , p'-y-first , p'-sim-non-y 
  with Alter-First p' x 
... | R'' , p'' , p''-x-first , p''-sim-non-x = (p'' ∷ v') 
    , true-agrees c-rem v' c'-x>y p'' x>y
    , false-agrees (InverseCoalition c-rem) v' inv'-y>x p''
    , (y>z , ea-y>z)
    , (p-x-z-sim , p-z-x-sim) , sim-x-z 
      where
        ¬y≡x : ¬ y ≡ x 
        ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x) 

        ¬z≡x : ¬ z ≡ x 
        ¬z≡x z≡x = ¬x≡z (Eq.sym z≡x) 

        ¬z≡y : ¬ z ≡ y 
        ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y)

        x>y : P p'' x y
        x>y = p''-x-first y ¬y≡x

        y>z : P p'' y z 
        y>z zR''y with p''-sim-non-x z y ¬z≡x ¬y≡x
        ... | R'→R'' , R''→R' = p'-y-first z ¬z≡y (R''→R' zR''y)

        p-z-x-sim : P→Bool p z x ≡ P→Bool p'' z x
        p-z-x-sim with R-dec p x z
        ... | inj₂ zPx = ⊥-elim (zPx (P→R p xPz)) 
        ... | inj₁ xRz with R-dec p'' x z
        ... | inj₁ xR''z = refl
        ... | inj₂ zP''x = ⊥-elim (zP''x (P→R p'' (p''-x-first z ¬z≡x)))

        p-x-z-sim : P→Bool p x z ≡ P→Bool p'' x z
        p-x-z-sim with R-dec p z x 
        ... | inj₁ zRx = ⊥-elim (xPz zRx)
        ... | inj₂ xPz with R-dec p'' z x 
        ... | inj₁ zR''x = ⊥-elim ((p''-x-first z ¬z≡x) zR''x)
        ... | inj₂ xP''z = refl

WeaklyDecisive-x>yImpliesDecisive-x>zSimilar (c ∷ c-rem) (p ∷ v) x y z ¬x≡z ¬y≡z ¬x≡y
  (false-agrees .c-rem .v ca-x>z .p)
  with WeaklyDecisive-x>yImpliesDecisive-x>zSimilar c-rem v x y z ¬x≡z ¬y≡z ¬x≡y ca-x>z
... | v' , c'-x>y , inv'-y>x , ea-y>z , sim-x-z
  with Alter-First p y -- y>x>z
... | _ , p' , p'-y-first , p'-sim-non-y = (p' ∷ v') 
    , false-agrees c-rem v' c'-x>y p'
    , true-agrees (InverseCoalition c-rem) v' inv'-y>x p' y>x
    , (p'-y-first z (λ z≡y → ¬y≡z (Eq.sym z≡y)) , ea-y>z)
    , (p-x-z-sim , p-z-x-sim) , sim-x-z
    where
        y>x : P p' y x 
        y>x = p'-y-first x ¬x≡y

        ¬z≡y : ¬ z ≡ y 
        ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y)

        p-x-z-sim : P→Bool p x z ≡ P→Bool p' x z
        p-x-z-sim with p'-sim-non-y z x ¬z≡y ¬x≡y 
        ... | R→R' , R'→R with R-dec p z x | R-dec p' z x
        ... | inj₁ zRx | inj₁ zR'x = refl
        ... | inj₁ zRx | inj₂ xP'z = ⊥-elim (xP'z (R→R' zRx))
        ... | inj₂ xPz | inj₁ zR'x = ⊥-elim (xPz (R'→R zR'x))
        ... | inj₂ xPz | inj₂ xP'z = refl

        p-z-x-sim : P→Bool p z x ≡ P→Bool p' z x
        p-z-x-sim with p'-sim-non-y x z ¬x≡y ¬z≡y
        ... | R→R' , R'→R with R-dec p x z | R-dec p' x z
        ... | inj₁ xRz | inj₁ xR'z = refl
        ... | inj₁ xRz | inj₂ zP'x = ⊥-elim (zP'x (R→R' xRz))
        ... | inj₂ zPx | inj₁ xR'z = ⊥-elim (zPx (R'→R xR'z))
        ... | inj₂ zPx | inj₂ zP'z = refl

WeaklyDecisive-x>yImpliesDecisive-x>z : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n m) 
         → SWF result
         → (x y z : Fin n)
         → ¬ (x ≡ z) 
         → ¬ (y ≡ z)
         → ¬ (x ≡ y)
         → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                 → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                 → result v' x y)
         → (CoalitionAgrees x z (Unwrap c) v)
         ------------------------------
         → result v x z
WeaklyDecisive-x>yImpliesDecisive-x>z {result = result} c v swf x y z ¬x≡z ¬y≡z ¬x≡y dec-x>y ca-x>z
  with WeaklyDecisive-x>yImpliesDecisive-x>zSimilar (Unwrap c) v x y z ¬x≡z ¬y≡z ¬x≡y ca-x>z 
... | v' , ca-x>y , inv-y>x , ea-y>z , sim-x-z = 
  BinaryIIA swf v v' x z sim-x-z
    (Transitive swf v' x y z 
      (dec-x>y v' ca-x>y inv-y>x)
      (Pareto swf v' y z ea-y>z)) 
CorollaryOne : {m : ℕ} 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n m)
             → SWF result
             → (x y z : Fin n)
             → ¬ x ≡ y 
             → ¬ y ≡ z
             → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                 → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                 → result v' x y)
             → CoalitionAgrees x z (Unwrap c) v
             ------------------------------
             → result v x z
CorollaryOne {n} c v swf x y z ¬x≡y ¬y≡z dec-x>y ca-x>z
  with x Fin.≟ z
... | true  because ofʸ  x≡z = 
  ⊥-elim (Decisive-x>x v c x z x≡z ca-x>z)
... | false because ofⁿ ¬x≡z = 
  WeaklyDecisive-x>yImpliesDecisive-x>z c v swf x y z ¬x≡z ¬y≡z ¬x≡y dec-x>y ca-x>z

WeaklyDecisive-x>yImpliesDecisive-z>ySimilar : {m : ℕ}
                  → (c : Coalition m) 
                  → (v : Votes n m) 
                  → (x y z : Fin n)
                  → ¬ (x ≡ z) 
                  → ¬ (y ≡ z)
                  → ¬ (x ≡ y)
                  → (CoalitionAgrees z y c v)
                  → Σ (Votes n m) 
                    λ v' → ((CoalitionAgrees x y c v') 
                         ×  (CoalitionAgrees y x (InverseCoalition c) v')
                         ×  (ElectionAgrees v' z x)
                         ×  (Similar m z y (Zipped z y v v')))
WeaklyDecisive-x>yImpliesDecisive-z>ySimilar [] [] x y z ¬x≡z ¬y≡z ¬x≡y empty-coalition-agrees 
  = [] , empty-coalition-agrees , empty-coalition-agrees , tt , tt
WeaklyDecisive-x>yImpliesDecisive-z>ySimilar (false ∷ c-rem) (p ∷ v) x y z ¬x≡z ¬y≡z ¬x≡y 
  (false-agrees .c-rem .v ca-z>y .p) 
  with WeaklyDecisive-x>yImpliesDecisive-z>ySimilar c-rem v x y z ¬x≡z ¬y≡z ¬x≡y ca-z>y 
... | v' , ca-x>y , inv-y>x , ea-z>x , sim-z-y 
  with Alter-Last p x 
... | R' , p' , p'-x-last , p'-sim-non-x = p' ∷ v' 
    , false-agrees c-rem v' ca-x>y p' 
    , true-agrees (InverseCoalition c-rem) v' inv-y>x p' (p'-x-last y ¬y≡x) 
    , (p'-x-last z ¬z≡x , ea-z>x) 
    , ((p-z-y-sim , p-y-z-sim) , sim-z-y)
    where 
      ¬y≡x : ¬ y ≡ x 
      ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x) 

      ¬z≡x : ¬ z ≡ x 
      ¬z≡x z≡x = ¬x≡z (Eq.sym z≡x) 

      p-z-y-sim : P→Bool p z y ≡ P→Bool p' z y
      p-z-y-sim with p'-sim-non-x y z ¬y≡x ¬z≡x 
      ... | R→R' , R'→R with R-dec p y z | R-dec p' y z 
      ... | inj₁ yRz | inj₁ yR'z = refl
      ... | inj₁ yRz | inj₂ zP'y = ⊥-elim (zP'y (R→R' yRz))
      ... | inj₂ zPy | inj₁ yR'z = ⊥-elim (zPy (R'→R yR'z))
      ... | inj₂ zPy | inj₂ zP'y = refl

      p-y-z-sim : P→Bool p y z ≡ P→Bool p' y z
      p-y-z-sim with p'-sim-non-x z y ¬z≡x ¬y≡x 
      ... | R→R' , R'→R with R-dec p z y | R-dec p' z y 
      ... | inj₁ zRy | inj₁ zR'y = refl
      ... | inj₁ zRy | inj₂ yP'z = ⊥-elim (yP'z (R→R' zRy))
      ... | inj₂ yPz | inj₁ zR'y = ⊥-elim (yPz (R'→R zR'y))
      ... | inj₂ yPz | inj₂ yP'z = refl
WeaklyDecisive-x>yImpliesDecisive-z>ySimilar (true ∷ c-rem) (p ∷ v) x y z ¬x≡z ¬y≡z ¬x≡y 
  (true-agrees .c-rem .v ca-z>y .p zPy) 
  with WeaklyDecisive-x>yImpliesDecisive-z>ySimilar c-rem v x y z ¬x≡z ¬y≡z ¬x≡y ca-z>y 
... | v' , ca-x>y , inv-y>x , ea-z>x , sim-z-y 
  with Alter-First p z 
... | R' , p' , p'-z-first , p'-sim-non-z 
  with Alter-Last p' y 
... | R'' , p'' , p''-y-last , p''-sim-non-y = p'' ∷ v' 
    , true-agrees c-rem v' ca-x>y p'' (p''-y-last x ¬x≡y) 
    , false-agrees (InverseCoalition c-rem) v' inv-y>x p'' 
    , (z>x , ea-z>x) 
    , ((p-z-y-sim , p-y-z-sim) , sim-z-y)
    where 
      ¬z≡y : ¬ z ≡ y 
      ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y) 

      z>x : P p'' z x 
      z>x xR''z with p''-sim-non-y x z ¬x≡y ¬z≡y 
      ... | R'→R'' , R''→R' = p'-z-first x ¬x≡z (R''→R' xR''z)

      p-z-y-sim : P→Bool p z y ≡ P→Bool p'' z y
      p-z-y-sim with R-dec p y z 
      ... | inj₁ yRz = ⊥-elim (zPy yRz)
      ... | inj₂ zPy with R-dec p'' y z 
      ... | inj₁ yR''z = ⊥-elim (p''-y-last z ¬z≡y yR''z)
      ... | inj₂ zP''y = refl 

      p-y-z-sim : P→Bool p y z ≡ P→Bool p'' y z
      p-y-z-sim with R-dec p z y
      ... | inj₂ yPz = ⊥-elim (zPy (P→R p yPz))
      ... | inj₁ zRy with R-dec p'' z y
      ... | inj₂ yP''z = ⊥-elim (⊥-elim (yP''z (P→R p'' (p''-y-last z ¬z≡y))))
      ... | inj₁ zR''y = refl

WeaklyDecisive-x>yImpliesDecisive-z>y : {m : ℕ} 
         → (c : NonEmptyCoalition m) 
         → (v : Votes n m) 
         → SWF result
         → (x y z : Fin n)
         → ¬ (x ≡ z) 
         → ¬ (y ≡ z)
         → ¬ (x ≡ y)
         → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                 → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                 → result v' x y)
         → CoalitionAgrees z y (Unwrap c) v
         ------------------------------
         → result v z y
WeaklyDecisive-x>yImpliesDecisive-z>y c v swf x y z ¬x≡z ¬y≡z ¬x≡y dec-x>y ca-z>y 
  with WeaklyDecisive-x>yImpliesDecisive-z>ySimilar (Unwrap c) v x y z ¬x≡z ¬y≡z ¬x≡y ca-z>y 
... | v' , ca-x>y , inv-y>x , ea-z>x , sim-z-y = 
  BinaryIIA swf v v' z y sim-z-y
    (Transitive swf v' z x y
      (Pareto swf v' z x ea-z>x)
      (dec-x>y v' ca-x>y inv-y>x)) 

CorollaryTwo : {m : ℕ} 
             → (c : NonEmptyCoalition m) 
             → (v : Votes n m) 
             → SWF result
             → (x y z : Fin n)
             → ¬ (x ≡ z)
             → ¬ (x ≡ y)
             → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                    → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                    → result v' x y)
             → CoalitionAgrees z y (Unwrap c) v
             ------------------------------
             → result v z y
CorollaryTwo c v swf x y z ¬x≡z ¬x≡y dec-x>y ca-z>y with z Fin.≟ y
... | true because ofʸ z≡y = ⊥-elim (Decisive-x>x v c z y z≡y ca-z>y)
... | false because ofⁿ ¬z≡y = 
  WeaklyDecisive-x>yImpliesDecisive-z>y c v swf x y z ¬x≡z ¬y≡z ¬x≡y dec-x>y ca-z>y
  where
    ¬y≡z : ¬ y ≡ z 
    ¬y≡z y≡z = ¬z≡y (Eq.sym y≡z) 

CorollaryThree : {m : ℕ}
               → (n ℕ.> 2)
               → (c : NonEmptyCoalition m) 
               → (v : Votes n m) 
               → SWF result
               → (x y : Fin n)
               → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                       → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                       → result v' x y)
               → CoalitionAgrees y x (Unwrap c) v
               ------------------------------
               → result v y x
CorollaryThree {n} (n>2) c v swf x y dec ca-y>x with x Fin.≟ y 
... | true because  ofʸ  x≡y 
  = ⊥-elim (Decisive-x>x v c y x (Eq.sym x≡y) ca-y>x)
... | false because ofⁿ ¬x≡y with FreshCandidate n n>2 x y 
... | z , ¬x≡z , ¬y≡z = 
  CorollaryOne c v swf y z x ¬y≡z ¬z≡x 
    (λ v' ca-y>z inv-z>y → 
      CorollaryTwo c v' swf x z y ¬x≡y ¬x≡z 
        (λ v'' ca-x>z _ → 
          CorollaryOne c v'' swf x y z ¬x≡y ¬y≡z dec ca-x>z) 
      ca-y>z) 
  ca-y>x 
    where
      ¬z≡x : ¬ z ≡ x 
      ¬z≡x z≡x = ¬x≡z (Eq.sym z≡x)

-- If a coalition is weakly deciisve for any pair of candidates, 
-- it is strictly decisive for all candidates.
ExpansionOfDecisiveness : {m : ℕ}
          → (n ℕ.> 2)
          → (c : NonEmptyCoalition m)
          → SWF result
          → (x y : Fin n)
          → ¬ x ≡ y 
          → (∀ v' → CoalitionAgrees x y (Unwrap c) v'
                  → CoalitionAgrees y x (InverseCoalition (Unwrap c)) v'
                  → result v' x y)
          → ∀ v a b → CoalitionAgrees a b (Unwrap c) v 
                    → result v a b
ExpansionOfDecisiveness {n} n>2 c swf x y ¬x≡y dec v a b ca-a>b
  with a Fin.≟ x | b Fin.≟ y 
... | true because ofʸ a≡x | false because ofⁿ ¬b≡y rewrite a≡x 
  = CorollaryOne c v swf x y b ¬x≡y ¬y≡b dec ca-a>b
    where 
      ¬y≡b : ¬ y ≡ b 
      ¬y≡b y≡b = ¬b≡y (Eq.sym y≡b)
... | false because ofⁿ ¬a≡x | true because ofʸ b≡y rewrite b≡y 
  = CorollaryTwo c v swf x y a ¬x≡a ¬x≡y dec ca-a>b
    where 
      ¬x≡a : ¬ x ≡ a
      ¬x≡a x≡a = ¬a≡x (Eq.sym x≡a)
... | true because ofʸ a≡x | true because ofʸ b≡y rewrite a≡x | b≡y 
  with FreshCandidate n n>2 x y 
... | z , ¬x≡z , ¬y≡z
  = CorollaryOne c v swf x z y ¬x≡z ¬z≡y (λ v' ca-x>z _ → 
      CorollaryTwo c v' swf y z x ¬y≡x ¬y≡z (λ v'' ca-y>z _ → 
        CorollaryOne c v'' swf y x z ¬y≡x ¬x≡z 
          (λ v'' ca-y>x _ → CorollaryThree n>2 c v'' swf x y dec ca-y>x)
        ca-y>z) 
      ca-x>z) 
    ca-a>b
  where 
    ¬z≡y : ¬ z ≡ y 
    ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y)
        
    ¬y≡x : ¬ y ≡ x 
    ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x)
ExpansionOfDecisiveness n>2 c swf x y ¬x≡y dec v a b ca-a>b | false because ofⁿ ¬a≡x | false because ofⁿ ¬b≡y 
  with b Fin.≟ x | a Fin.≟ y 
... | false because ofⁿ ¬b≡x | false because ofⁿ ¬a≡y = 
  CorollaryOne c v swf a x b ¬a≡x ¬x≡b (λ v' ca-a>x _ → 
    CorollaryTwo c v' swf y x a ¬y≡a ¬y≡x (λ v'' ca-y>x _ → 
      CorollaryThree n>2 c v'' swf x y dec ca-y>x)
    ca-a>x) 
  ca-a>b
  where
    ¬x≡b : ¬ x ≡ b 
    ¬x≡b x≡b = ¬b≡x (Eq.sym x≡b)
    
    ¬y≡x : ¬ y ≡ x 
    ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x)

    ¬y≡a : ¬ y ≡ a 
    ¬y≡a y≡a = ¬a≡y (Eq.sym y≡a)    
... | false because ofⁿ ¬b≡x | true because ofʸ a≡y rewrite a≡y = 
  CorollaryTwo c v swf x b y ¬x≡y ¬x≡b (λ v' ca-x>b _ → 
    CorollaryOne c v' swf x y b ¬x≡y ¬y≡b dec ca-x>b) 
  ca-a>b
    where
      ¬x≡b : ¬ x ≡ b
      ¬x≡b x≡b = ¬b≡x (Eq.sym x≡b)

      ¬y≡b : ¬ y ≡ b
      ¬y≡b y≡b = ¬b≡y (Eq.sym y≡b)
... | true because ofʸ b≡x | false because ofⁿ ¬a≡y rewrite b≡x = 
  CorollaryOne c v swf a y x ¬a≡y ¬y≡x 
    (λ v' ca-a>y _ → CorollaryTwo c v' swf x y a ¬x≡a ¬x≡y dec ca-a>y) 
  ca-a>b
  where 
      ¬x≡a : ¬ x ≡ a
      ¬x≡a x≡a = ¬a≡x (Eq.sym x≡a)
      ¬y≡x : ¬ y ≡ x 
      ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x)
... | true because ofʸ b≡x | true because ofʸ a≡y rewrite b≡x | a≡y 
  = CorollaryThree n>2 c v swf x y dec ca-a>b

ConstructCoalition : {m s : ℕ}
                   → (c : Coalition m)
                   → (MembersCount c ≡ (suc s))
                   → Σ (SingletonCoalition m) λ (c' , _) →
                      Σ (Coalition m) λ c'' → (MembersCount c'' ≡ s)
                        × c ≡ zipWith _xor_ c' c''
ConstructCoalition (false ∷ c) mc with ConstructCoalition c mc 
... | (head , is-single) , (tail , is-tail , isxor) rewrite isxor
    = ((false ∷ head) , is-single) 
    , (false ∷ tail) , is-tail
    , refl
ConstructCoalition {m = suc m'} {s = s} (true ∷ c) mc
  = ((true ∷ FalseCoalition m') , HeadIsSingleton m') 
  , (false ∷ c) , mc' 
  , ContractionOfDecisiveCoalitionIsXor m' c
    where
      mc' : MembersCount (false ∷ c) ≡ s
      mc' with MembersCount c
      ... | mc'' = suc-injective mc

      FalseMembersCount : ∀ m → MembersCount (FalseCoalition m) ≡ 0
      FalseMembersCount zero = refl
      FalseMembersCount (suc m) rewrite FalseMembersCount m = refl

      HeadIsSingleton : ∀ m → MembersCount (true ∷ FalseCoalition m) ≡ 1
      HeadIsSingleton m rewrite FalseMembersCount m = refl

      ContractionOfDecisiveCoalitionIsXor : ∀ m' (c : Coalition m') → _≡_ {A = Vec Bool (suc m')} (true ∷ c) (true ∷ zipWith _xor_ (FalseCoalition m') c)
      ContractionOfDecisiveCoalitionIsXor m' c rewrite Eq.sym (isXor {m = m'} c) = refl
ConstructVotes : {m : ℕ} 
               → (x y z : Fin n)
               → ¬ (x ≡ y)
               → ¬ (x ≡ z) 
               → ¬ (y ≡ z)
               → ∀ c c' c''  
               → (c ≡ zipWith _xor_ c' c'')
               → Σ (Votes n m) 
               λ v → (CoalitionAgrees x y c v)
                   × (CoalitionAgrees x z c' v)
                   × (CoalitionAgrees z x (InverseCoalition c') v)
                   × (CoalitionAgrees z y c'' v)
                   × (CoalitionAgrees y z (InverseCoalition c'') v)
ConstructVotes _ _ _ _ _ _ [] [] [] zipwith = [] 
  , empty-coalition-agrees 
  , empty-coalition-agrees 
  , empty-coalition-agrees 
  , empty-coalition-agrees 
  , empty-coalition-agrees
ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z (false ∷ c) (false ∷ c') (false ∷ c'') zipwithEq
  with ∷-injectiveʳ zipwithEq
... | zipwithEq' with ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z c c' c'' zipwithEq' 
... | v' , c-x>y , c'-x>z , inv'-z>x , c''-z>y , inv'-y>z
    with Alter-First TrivialVoter y
... | R , p , y-first , p-sim-non-y
    with Alter-Last p x
... | R' , p' , x-last , p'-sim-non-x
    = (p' ∷ v') -- y>z>x
    , false-agrees c v' c-x>y p'
    , false-agrees c' v' c'-x>z p'
    , true-agrees (InverseCoalition c') v' inv'-z>x p' (x-last z ¬z≡x) 
    , false-agrees c'' v' c''-z>y p'
    , true-agrees (InverseCoalition c'') v' inv'-y>z p' y>z
    where
      ¬z≡x : ¬ z ≡ x 
      ¬z≡x z≡x = ¬x≡z (Eq.sym z≡x) 
      
      ¬z≡y : ¬ z ≡ y
      ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y) 

      ¬y≡x : ¬ y ≡ x 
      ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x) 

      y>z : P p' y z
      y>z zR'y with p'-sim-non-x z y ¬z≡x ¬y≡x 
      ... | _ , R'→R = y-first z ¬z≡y (R'→R zR'y)
ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z (false ∷ c) (true ∷ c') (true ∷ c'') zipwithEq 
  with ∷-injectiveʳ zipwithEq
... | zipwithEq' with ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z c c' c'' zipwithEq' 
... | v' , c-x>y , c'-x>z , inv'-z>x , c''-z>y , inv'-y>z    
    with Alter-First TrivialVoter x
... | R , p , x-first , p-sim-non-x 
    with Alter-Last p y
... | R' , p' , y-last , p'-sim-non-y
    = (p' ∷ v') -- x>z>y
    , false-agrees c v' c-x>y p'
    , true-agrees c' v' c'-x>z p' x>z
    , false-agrees (InverseCoalition c') v' inv'-z>x p' 
    , true-agrees c'' v' c''-z>y p' (y-last z ¬z≡y)  
    , false-agrees (InverseCoalition c'') v' inv'-y>z p'
    where
      ¬z≡y : ¬ z ≡ y
      ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y) 
      
      ¬z≡x : ¬ z ≡ x 
      ¬z≡x z≡x = ¬x≡z (Eq.sym z≡x) 

      x>z : P p' x z
      x>z zR'x with p'-sim-non-y z x ¬z≡y ¬x≡y 
      ... | _ , R'→R = x-first z ¬z≡x (R'→R zR'x)
ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z (true ∷ c) (false ∷ c') (true ∷ c'') zipwithEq 
  with ∷-injectiveʳ zipwithEq
... | zipwithEq' with ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z c c' c'' zipwithEq' 
... | v' , c-x>y , c'-x>z , inv'-z>x , c''-z>y , inv'-y>z     
  with Alter-First TrivialVoter z
... | R , p , z-first , p-sim-non-z
    with Alter-Last p y
... | R' , p' , y-last , p'-sim-non-y
    = (p' ∷ v') -- z>x>y
    , true-agrees c v' c-x>y p' (y-last x ¬x≡y)
    , false-agrees c' v' c'-x>z p'
    , true-agrees (InverseCoalition c') v' inv'-z>x p' z>x 
    , true-agrees c'' v' c''-z>y p' (y-last z ¬z≡y) 
    , false-agrees (InverseCoalition c'') v' inv'-y>z p'
    where
      ¬z≡y : ¬ z ≡ y
      ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y) 

      z>x : P p' z x
      z>x xR'z with p'-sim-non-y x z ¬x≡y ¬z≡y 
      ... | _ , R'→R = z-first x ¬x≡z (R'→R xR'z)
ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z (true ∷ c) (true ∷ c') (false ∷ c'') zipwithEq 
  with ∷-injectiveʳ zipwithEq
... | zipwithEq' with ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z c c' c'' zipwithEq' 
... | v' , c-x>y , c'-x>z , inv'-z>x , c''-z>y , inv'-y>z
    with Alter-First TrivialVoter x
... | R , p , x-first , p-sim-non-x
    with Alter-Last p z
... | R' , p' , z-last , p'-sim-non-z 
    = (p' ∷ v') -- x>y>z
    , true-agrees c v' c-x>y p' x>y
    , true-agrees c' v' c'-x>z p' (z-last x ¬x≡z)
    , false-agrees (InverseCoalition c') v' inv'-z>x p' 
    , false-agrees c'' v' c''-z>y p'
    , true-agrees (InverseCoalition c'') v' inv'-y>z p' (z-last y ¬y≡z)
    where
      ¬y≡x : ¬ y ≡ x 
      ¬y≡x y≡x = ¬x≡y (Eq.sym y≡x) 

      x>y : P p' x y 
      x>y yR'x with p'-sim-non-z y x ¬y≡z ¬x≡z 
      ... | _ , R'→R = x-first y ¬y≡x (R'→R yR'x) 

ContractionOfDecisiveCoalitionSimilar : {m s : ℕ}
               → (c : Coalition m)
               → (MembersCount c ≡ (suc s))
               → (x y z : Fin n)
               → ¬ (x ≡ y)
               → ¬ (x ≡ z) 
               → ¬ (y ≡ z)
               → Σ (Votes n m) 
                λ v → Σ (SingletonCoalition m)
                  λ (c' , _) → Σ (Coalition m) 
                    λ c'' → (MembersCount c'' ≡ s)
                      × (CoalitionAgrees x y c v)
                      × (CoalitionAgrees x z c' v)
                      × (CoalitionAgrees z x (InverseCoalition c') v)
                      × (CoalitionAgrees z y c'' v)
                      × (CoalitionAgrees y z (InverseCoalition c'') v)
ContractionOfDecisiveCoalitionSimilar {n = n} c mc x y z ¬x≡y ¬x≡z ¬y≡z 
  with ConstructCoalition c mc 
... | (head , single) , tail , is-smaller , isxor 
  with ConstructVotes x y z ¬x≡y ¬x≡z ¬y≡z c head tail isxor 
... | v' , c-x>y , c'-x>z , inv'-z>x , c''-z>y , inv'-y>z = v' 
    , (head , single) , tail , is-smaller 
    , c-x>y , c'-x>z , inv'-z>x , c''-z>y , inv'-y>z

SimilarHelper : {m n : ℕ} 
              → (v v' : Votes n m)
              → (x y : Fin n) 
              → (c : Coalition m) 
              → CoalitionAgrees x y c v
              → CoalitionAgrees x y c v'
              → CoalitionAgrees y x (InverseCoalition c) v
              → CoalitionAgrees y x (InverseCoalition c) v'
              → Similar m x y (Zipped x y v v')
SimilarHelper [] [] x y [] ca-x>y ca'-x>y inv-y>x inv'-y>x = tt
SimilarHelper (p ∷ v) (p' ∷ v') x y (false ∷ c) 
  (false-agrees .c .v ca-x>y .p) 
  (false-agrees .c .v' ca'-x>y .p')
  (true-agrees .(InverseCoalition c) .v inv-y>x .p yPx) 
  (true-agrees .(InverseCoalition c) .v' inv'-y>x .p' yP'x) 
  = (sim-x-y , sim-y-x) 
  , (SimilarHelper v v' x y c ca-x>y ca'-x>y inv-y>x inv'-y>x)
    where 
    sim-y-x : P→Bool p y x ≡ P→Bool p' y x
    sim-y-x with R-dec p x y
    ... | inj₁ xRy = ⊥-elim (yPx xRy)
    ... | inj₂ yPx with R-dec p' x y 
    ... | inj₁ xR'y = ⊥-elim (yP'x xR'y)
    ... | inj₂ yP'x = refl

    sim-x-y : P→Bool p x y ≡ P→Bool p' x y
    sim-x-y with R-dec p y x
    ... | inj₂ xPy = ⊥-elim (yPx (P→R p xPy))
    ... | inj₁ yRx with R-dec p' y x 
    ... | inj₁ yR'x = refl
    ... | inj₂ xP'y = ⊥-elim (yP'x (P→R p' xP'y))
SimilarHelper (p ∷ v) (p' ∷ v') x y (true ∷ c) 
  (true-agrees .c .v ca-x>y .p xPy) 
  (true-agrees .c .v' ca'-x>y .p' xP'y) 
  (false-agrees .(InverseCoalition c) .v inv-y>x .p) 
  (false-agrees .(InverseCoalition c) .v' inv'-y>x .p') 
  = (sim-x-y , sim-y-x) 
  , (SimilarHelper v v' x y c ca-x>y ca'-x>y inv-y>x inv'-y>x)
  where 
    sim-y-x : P→Bool p y x ≡ P→Bool p' y x
    sim-y-x with R-dec p x y
    ... | inj₂ yPx = ⊥-elim (xPy (P→R p yPx))
    ... | inj₁ xRy with R-dec p' x y 
    ... | inj₁ xR'y = refl
    ... | inj₂ yP'x = ⊥-elim (xP'y (P→R p' yP'x))

    sim-x-y : P→Bool p x y ≡ P→Bool p' x y
    sim-x-y with R-dec p y x
    ... | inj₁ yRx = ⊥-elim (xPy yRx)
    ... | inj₂ xPy with R-dec p' y x 
    ... | inj₁ yR'x = ⊥-elim (xP'y yR'x)
    ... | inj₂ xP'y = refl

-- Every coalition of size greater than 2 
-- has a strict subset that is decisive over a pair of candidates.
ContractionOfDecisiveCoalition : {m s : ℕ}
          → (n ℕ.> 2)
          → (c : Coalition m) 
          → (MembersCount c ≡ (suc s))
          → (x y z : Fin n)
          → ¬ (x ≡ y)
          → ¬ (x ≡ z) 
          → ¬ (y ≡ z)
          → (∀ v' → CoalitionAgrees x y c v'
                  → result v' x y)
          → SWF result
          → (Σ (SingletonCoalition m)
             λ (c' , _) → (∀ v' → CoalitionAgrees x z c' v'
                                → CoalitionAgrees z x (InverseCoalition c') v'
                                → result v' x z))
          ⊎ (Σ (Coalition m) 
             λ c' → (MembersCount c' ≡ s)
                        × (∀ v' → CoalitionAgrees z y c' v'
                                → CoalitionAgrees y z (InverseCoalition c') v'
                                → result v' z y))
ContractionOfDecisiveCoalition {n} {m = m} {s = zero} n>2 c mc x y z ¬x≡y ¬x≡z ¬y≡z dec-x>y swf 
  = inj₁ ((c , mc) 
  , (λ v' ca-x>z _ → ExpansionOfDecisiveness n>2 (c , (Singleton→NonEmpty (c , mc))) 
    swf x y ¬x≡y (λ v'' ca-x>y _ → dec-x>y v'' ca-x>y) v' x z ca-x>z))
ContractionOfDecisiveCoalition {n} {m = m} {s = suc s} n>2 c mc x y z ¬x≡y ¬x≡z ¬y≡z dec-x>y swf
  with ContractionOfDecisiveCoalitionSimilar {s = suc s} c mc x y z ¬x≡y ¬x≡z ¬y≡z
... | v' 
    , (c' , is-single) 
    , c'' , is-smaller 
    , c-x>y 
    , c'-x>z , inv-c'-z>x 
    , c''-z>y , inv-c''-y>z with Complete swf v' y z ¬y≡z
... | inj₁ yPz = inj₁ ((c' , is-single) 
    , λ v'' c-x>z inv-z>x → BinaryIIA swf v'' v' x z 
      (SimilarHelper v'' v' x z c' c-x>z c'-x>z inv-z>x inv-c'-z>x) 
      (Transitive swf v' x y z (dec-x>y v' c-x>y) yPz))
... | inj₂ zPy = inj₂ (c'' , is-smaller
    , λ v'' c-z>y inv-y>z → BinaryIIA swf v'' v' z y 
      (SimilarHelper v'' v' z y c'' c-z>y c''-z>y inv-y>z inv-c''-y>z) 
    zPy)

ContractionOfDecisiveCoalitionWrapper : {m s : ℕ}
         → (n ℕ.> 2)
         → (c : Coalition m) 
         → (MembersCount c ≡ (suc s))
         → (x y : Fin n)
         → ¬ x ≡ y 
         → (∀ v' → CoalitionAgrees x y c v'
                 → result v' x y)
         → SWF result
         → (v : Votes n m) 
         → Dictator v result
ContractionOfDecisiveCoalitionWrapper {n} {m = zero} (s≤s (s≤s n>2)) [] mc x y _ _ swf v' = 
  ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
ContractionOfDecisiveCoalitionWrapper {n} {result = result} {m = suc m} {zero} n>2 c mc x y ¬x≡y dec swf v 
  = (c , mc) , ExpansionOfDecisiveness n>2 (c , (Singleton→NonEmpty (c , mc))) 
    swf x y ¬x≡y (λ v'' ca-x>y _ → dec v'' ca-x>y) v
ContractionOfDecisiveCoalitionWrapper {n} {result = result} {m = suc m} {suc s} n>2 c mc x y ¬x≡y dec swf v 
  with FreshCandidate n n>2 x y 
... | z , ¬x≡z , ¬y≡z with ContractionOfDecisiveCoalition n>2 c mc x y z ¬x≡y ¬x≡z ¬y≡z dec swf
... | inj₁ ((c' , mc') , is-dec) rewrite mc' = (c' , mc') 
    , (ExpansionOfDecisiveness n>2 (c' , Singleton→NonEmpty (c' , mc')) swf x z ¬x≡z is-dec v)
... | inj₂ (c' , is-smaller , is-dec) = 
  ContractionOfDecisiveCoalitionWrapper {s = s} n>2 c' is-smaller z y ¬z≡y 
    (λ v' → ExpansionOfDecisiveness n>2 (c' , mc') swf z y ¬z≡y is-dec v' z y) 
  swf v 
  where
    ¬z≡y : ¬ z ≡ y 
    ¬z≡y z≡y = ¬y≡z (Eq.sym z≡y) 

    mc' : MembersCount c' ℕ.> 0
    mc' rewrite is-smaller = s≤s z≤n 

ArrowsTheorem : {m : ℕ}
              → (n ℕ.> 2)
              → (v : Votes n m)
              → SWF result
              → Dictator v result
ArrowsTheorem {n} {m = zero} (s≤s (s≤s n>2)) [] swf 
  = ⊥-elim (SWF.Asymmetric swf [] zero (suc zero) 
    (SWF.Pareto swf [] zero (suc zero) tt) 
    (SWF.Pareto swf [] (suc zero) zero tt))
ArrowsTheorem {n} {result = result} {m = (suc m)} (s≤s (s≤s n>2)) v swf = 
  ContractionOfDecisiveCoalitionWrapper {result = result} {s = m} (s≤s (s≤s n>2))
    (Whole (suc m)) (sizeOfWholem≡m m) zero (suc zero) (λ ()) 
      (λ v' → WholeIsDecisive v' swf zero (suc zero)) swf v
  where
    sizeOfWholem≡m : (m : ℕ) → MembersCount (Whole (suc m)) ≡ suc m
    sizeOfWholem≡m zero = refl
    sizeOfWholem≡m (suc m) rewrite sizeOfWholem≡m m = refl
         