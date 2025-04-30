{-# OPTIONS --rewriting #-}
module Decisive where

open import Voter
open import Votes
open import Election
open import Coalition
open WeakPreference
open StrictPreference

open import Data.Fin as Fin using (_≟_; Fin)
open import Data.Nat as ℕ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit

private
    variable
        m n : ℕ

-- A coalition is decisive 
-- if a proof that every member of the coalition prefers a to b
-- implies that the set of voters prefers a to b.
Decisive : Coalition m
         → (v : Votes n m) 
         → (Votes n m → Fin n → Fin n → Set)
         → Set₁
Decisive c v result = ∀ a b 
  → (CoalitionAgrees a b c v) 
  → result v a b

-- A voter is a dictator if they are the only member of a decisive coalition.
Dictator : (v : Votes n m) 
         → (Votes n m → Fin n → Fin n → Set)
         → Set₁
Dictator {m = m} v result = 
  Σ (SingletonCoalition m) 
    λ c → Decisive (c .proj₁) v result