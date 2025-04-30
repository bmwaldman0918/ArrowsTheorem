module Votes where
  
open import Voter
open WeakPreference
open StrictPreference
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕProp using (≤∧≢⇒<; <⇒≤; ≤-reflexive; n<1+n)
open import Data.Fin as Fin hiding (_+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Empty
open import Data.Bool
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)

-- A votes object is a vector of preferences.
-- It is not actually a vector because Agda does not allow vectors of functions
data Votes (n : ℕ) : ℕ → Set₁ where
  []  : Votes n 0
  _∷_ : {_R_ : Fin n → Fin n → Set} → {m : ℕ} 
      → Preference n _R_ 
      → Votes n m 
      → Votes n (suc m)
open Votes


Length : {n m : ℕ} → Votes n m → ℕ
Length {m = m} _ = m

-- A zip object is used to evaluate pairwise equality for vectors
data Zip {n : ℕ} (a b : Fin n) : ℕ → Set₁ where
  z-nil : Zip a b 0
  z-cons : {r1 r2 : Fin n → Fin n → Set} 
         → {m : ℕ} 
         → (p1 : Preference n r1) 
         → (p2 : Preference n r2)
         → Zip a b m
         -----------
         → Zip a b (suc m)

Zipped : {m n : ℕ}
       → (a b : Fin n) 
       → (v1 v2 : Votes n m) 
       → Zip a b m
Zipped a b [] [] = z-nil
Zipped a b (x ∷ v1) (y ∷ v2) = z-cons x y (Zipped a b v1 v2)

-- An object of type similar is a proof 
-- that two votes objects have pairwise equal preferences for two candidates.
-- It is used to apply IIA.
Similar : {n : ℕ} 
        → (m : ℕ) 
        → (a b : Fin n) 
        → Zip a b m 
        → Set
Similar .0 a b z-nil = ⊤
Similar (suc m) a b (z-cons p1 p2 zip) = 
  ((P→Bool p1 a b ≡ P→Bool p2 a b) 
 × (P→Bool p1 b a ≡ P→Bool p2 b a))
 × (Similar m a b zip)

-- An election agrees object is a proof that 
-- all voters in an election prefer one candidate to another
ElectionAgrees : {m n : ℕ} 
               → (v : Votes n m) 
               → (a b : Fin n) 
               → Set
ElectionAgrees [] a b = ⊤ 
ElectionAgrees {m = suc m'} (x ∷ v) a b = P x a b × (ElectionAgrees v a b) 