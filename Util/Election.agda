module Util.Election where

open import Util.Voter
open WeakPreference using (Preference)
open import Util.Votes

open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Vec as Vec
open import Data.Bool as Bool
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Unit

private
    variable
        m n : ℕ
        n>2 : n ℕ.> 2
        a b c : Fin n
        Result : Fin n → Fin n → Set

-- An SWF (or social welfare function) represents a final ranking of candidates.
-- We postulate that it is decidable, transitive, complete and asymmetric. 
-- In other words, it is a strict order.
-- We also postulate that it satisfies Pareto efficiency and IIA.

record SWF {n : ℕ} (Result : {m : ℕ} → Votes n m → Fin n → Fin n → Set) : Set₁ where
  field
    Pareto      : {m : ℕ} 
                → (v : Votes n m) 
                → (a b : Fin n)   
                → ElectionAgrees v a b 
                → Result v a b 

    BinaryIIA   : {m : ℕ} 
                → (v v' : Votes n m)
                → (a b : Fin n)
                → Similar m a b (Zipped a b v v')
                → Result v' a b
                → Result v a b

    Transitive  : {m : ℕ} 
                → (v : Votes n m) 
                → (a b c : Fin n) 
                → Result v a b 
                → Result v b c 
                → Result v a c

    Complete    : {m : ℕ} 
                → (v : Votes n m) 
                → (a b : Fin n)
                → ¬ (a ≡ b) 
                → (Result v a b) 
                ⊎ (Result v b a)

    Decidable   : {m : ℕ} 
                → (v : Votes n m) 
                → (a b : Fin n)   
                →   (Result v a b) 
                ⊎ ¬ (Result v a b)

    Asymmetric  : {m : ℕ} 
                → (v : Votes n m) 
                → (a b : Fin n)
                → Result v a b
                → ¬ Result v b a
