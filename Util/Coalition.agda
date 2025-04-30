{-# OPTIONS --rewriting #-}
module Util.Coalition where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Vec as Vec
open import Data.Bool using (Bool; not; true; false; _≟_; _xor_)
open import Data.Nat as ℕ hiding (_≟_)
open import Util.Votes
open import Data.Fin as Fin hiding (_≟_)
open import Data.Product using (Σ; _×_; _,_; proj₂; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Util.Voter
open WeakPreference
open StrictPreference

-- A coalition is a mask applied to a set of votes.
Coalition : ℕ → Set
Coalition m = Vec Bool m

MembersCount : {m : ℕ} → Vec Bool m → ℕ
MembersCount c = count (λ x → x ≟ true) c

-- The inverse of a coalition is all voters not in the coalition.
InverseCoalition : {m : ℕ} → Coalition m → Coalition m
InverseCoalition [] = []
InverseCoalition (h ∷ c) = not h ∷ (InverseCoalition c)

-- A coalition agrees object is a proof 
-- that all members of a coalition strictly prefer a to b.
data CoalitionAgrees {n : ℕ} (a b : Fin n) : 
    {m : ℕ} 
  → (c : Coalition m) 
  → (v2 : Votes n m) 
  → Set₁ where
    empty-coalition-agrees : CoalitionAgrees a b [] []
    
    false-agrees : {m : ℕ} 
                 → (c : Coalition m) 
                 → (v : Votes n m)
                 → {_R_ : Fin n → Fin n → Set} 
                 → CoalitionAgrees a b c v 
                 → (p : Preference n _R_) 
                 → CoalitionAgrees a b (false Vec.∷ c) (p ∷ v)

    true-agrees : {m : ℕ} 
                → (c : Coalition m) → (v : Votes n m)
                → {_R_ : Fin n → Fin n → Set} 
                → CoalitionAgrees a b c v 
                → (p : Preference n _R_)
                → (P p a b)
                → CoalitionAgrees a b (true Vec.∷ c) (p ∷ v)

-- The coalition of the whole contains all voters.
Whole : (m : ℕ) → (Coalition m)
Whole zero = [] 
Whole (suc m) = true ∷ (Whole m) 

-- A nonempty coalition contains at least one member.
NonEmptyCoalition : (m : ℕ) → Set
NonEmptyCoalition m = Σ (Coalition m) λ c → MembersCount c ℕ.> 0

Unwrap : {m : ℕ} → NonEmptyCoalition m → Coalition m
Unwrap (fst , _) = fst

-- A singleton coalition contains exactly one member.
SingletonCoalition : (m : ℕ) → Set
SingletonCoalition m = Σ (Coalition m) λ c → MembersCount c ≡ 1

Singleton→NonEmpty : {m : ℕ} 
                   → (c : SingletonCoalition m)
                   → (MembersCount (c .proj₁)) ℕ.> 0
Singleton→NonEmpty (fst , snd) rewrite snd = s≤s z≤n

FalseCoalition : (n : ℕ) → Coalition n
FalseCoalition zero    = []
FalseCoalition (suc n) = false ∷ FalseCoalition n

isXor : {m : ℕ} → (c : Coalition m) → c ≡ (zipWith _xor_ (FalseCoalition m) c)
isXor [] = refl
isXor (x ∷ c) rewrite Eq.sym (isXor c) = refl