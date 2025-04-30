module Voter where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_; Dec; _because_; ofⁿ; ofʸ)
open import Data.Empty
open import Data.Bool using (true; false; Bool)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)

private
    variable
        n : ℕ
        n>2 : n ℕ.> 2
        a b c : Fin n
        _R_ : Fin n → Fin n → Set

module WeakPreference where
    --- A weak preference is transitive, complete, and decidable relation
    --- A weak preference is not anti-symmetric, so voters can be indifferent between candidates
    record Preference (n : ℕ) (_R_ : Fin n → Fin n → Set) : Set where
        field
            R-trans    : (a b c : Fin n) → a R b → b R c → a R c
            R-complete : (a b : Fin n)   → (a R b) ⊎   (b R a)
            R-dec      : (a b : Fin n)   → (a R b) ⊎ ¬ (a R b)
    open Preference

    --- Weak preferences are reflexive
    R-refl : (v : Preference n _R_) 
        → (a b : Fin n)
        → (a ≡ b) 
        ----------------------
        → a R b
    R-refl v a b a≡b with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa rewrite a≡b = bRa

    ¬R-dec→⊥ : {p : Preference n _R_} → {a b : Fin n} → ¬ (a R b) → ¬ (b R a) → ⊥
    ¬R-dec→⊥ {p = p} {a = a} {b = b} ¬aRb ¬bRa with R-complete p a b 
    ... | inj₁ aRb = ¬aRb aRb
    ... | inj₂ bRa = ¬bRa bRa

    R→Bool : (p : Preference n _R_) → (a b : Fin n) → Bool
    R→Bool p a b with R-dec p a b 
    ... | inj₁ x = true
    ... | inj₂ y = false

    module StrictPreference where
    --- Strict preferences are the absence of the inverted weak preference
    P : (Preference n _R_) 
        → (a b : Fin n) 
        ----------------------
        → Set
    P {_R_ = _R_} _ a b = ¬ (b R a)

    --- Strict preferences imply weak preferences
    P→R : {a b : Fin n} 
        → (v : Preference n _R_)
        → (P v a b) 
        --------------------------
        → a R b
    P→R {a = a} {b = b} v ¬bRa with R-complete v a b
    ... | inj₁ aRb = aRb
    ... | inj₂ bRa = ⊥-elim (¬bRa bRa)

    --- Strict preferences imply inequality
    P↛≡ : (v : Preference n _R_)
        → (P v a b) 
        --------------------------
        → ¬ (a ≡ b)
    P↛≡ {a = a} {b = b} v ¬bRb a≡b = ¬bRb (R-refl v b a (Eq.sym a≡b))

    --- Strict preference is transitive
    P-trans : {v : Preference n _R_} 
            → P v a b 
            → P v b c 
            --------------------------
            → P v a c
    P-trans {a = a} {b = b} {c = c} {v = v} 
        with (R-dec v a b) | (R-complete v a b) 
    ...      | inj₁ aRb    | _        = 
      λ  bRc ¬cRb cRa → ¬cRb (R-trans v c a b cRa aRb)
    ...      | inj₂ ¬aRb   | inj₁ aRb = 
      λ ¬bRa ¬cRb cRa → ⊥-elim (¬aRb aRb)
    ...      | _           | inj₂ bRa = 
      λ ¬bRa ¬cRb cRa → ⊥-elim (¬bRa bRa)

    P→Bool : (p : Preference n _R_) → (a b : Fin n) → Bool
    P→Bool p a b with R-dec p b a 
    ... | inj₁ x = false
    ... | inj₂ y = true
open WeakPreference
open Preference
open StrictPreference
  
module AlteredVoters where
  -- Altered voters are provably identical to a given voter 
  -- except they have moved a specific candidate to first or last on their ballot
  Alter-Last : {_R_ : Fin n → Fin n → Set}
             → (p : Preference n _R_)
             → (z : Fin n)
             → Σ (Fin n → Fin n → Set) λ _R'_ 
               → Σ (Preference n _R'_) 
                 λ p' → (∀ a   → ¬ a ≡ z → P p' a z)
                      × (∀ x y → ¬ x ≡ z → ¬ y ≡ z
                               → (x R  y → x R' y)
                               × (x R' y → x R  y))
  Alter-Last {n = n} {_R_ = _R_} p z 
    = _R'_ , (p' , (λ {a ¬a≡z (z-last .a) → ¬a≡z Eq.refl
                    ; a ¬a≡z (original .z .a ¬z≡z _) → ¬z≡z Eq.refl}) 
                , agree-non-z) 
    where
      data _R'_ : Fin n → Fin n → Set where
        z-last   : ∀ a                     → a R' z 
        original : ∀ a b → ¬ a ≡ z → a R b → a R' b
        
      R'-trans : ∀ a b c → a R' b → b R' c → a R' c
      R'-trans a b c _ (z-last .b) = z-last a
      R'-trans a b c (z-last .a) (original .b .c ¬z≡z _) = ⊥-elim (¬z≡z Eq.refl)
      R'-trans a b c (original .a .b ¬a≡z aRb) (original .b .c _ bRc) 
        = original a c ¬a≡z (R-trans p a b c aRb bRc)

      R'-complete : ∀ a b → (a R' b) ⊎ (b R' a)
      R'-complete a b with a Fin.≟ z | b Fin.≟ z | R-complete p a b 
      ... | false because ofⁿ ¬a≡z | _ | inj₁ aRb 
        = inj₁ (original a b ¬a≡z aRb)
      ... | false because ofⁿ ¬a≡z | false because ofⁿ ¬b≡z | inj₂ bRa 
        = inj₂ (original b a ¬b≡z bRa)
      ... | _ | true because ofʸ b≡z | _ rewrite b≡z = inj₁ (z-last a)
      ... | true because ofʸ a≡z | _ | _ rewrite a≡z = inj₂ (z-last b)
      
      R'-dec : ∀ a b → (a R' b) ⊎ ¬ (a R' b)
      R'-dec a b with a Fin.≟ z | b Fin.≟ z | R-dec p a b 
      ... | false because ofⁿ ¬a≡z | _ | inj₁ aRb 
        = inj₁ (original a b ¬a≡z aRb)
      ... | false because ofⁿ ¬a≡z | false because ofⁿ ¬b≡z | inj₂ bPa 
        = inj₂ (λ {(z-last .a) → ¬b≡z Eq.refl
                ; (original .a .b _ aRb) → bPa aRb})
      ... | _ | true  because ofʸ  b≡z | _ rewrite b≡z = inj₁ (z-last a)
      ... | true because ofʸ a≡z | false because ofⁿ ¬b≡z | _ rewrite a≡z 
        = inj₂ (λ {(z-last .z) → ¬b≡z Eq.refl
                ; (original .z .b ¬z≡z _) → ¬z≡z Eq.refl})

      p' : Preference n _R'_
      p' = record { 
          R-trans    = R'-trans 
        ; R-complete = R'-complete 
        ; R-dec      = R'-dec }
      
      agree-non-z : ∀ x y → (¬ x ≡ z) → (¬ y ≡ z) 
                  → (x R y → x R' y) × (x R' y → x R y)
      agree-non-z x y ¬x≡z ¬y≡z = (λ xRy → original x y ¬x≡z xRy) 
                                , (λ {(z-last .x) → ⊥-elim (¬y≡z Eq.refl)
                                    ; (original .x .y _ xRy) → xRy})

  Alter-First : {_R_ : Fin n → Fin n → Set}
                → (p : Preference n _R_)
                → (z : Fin n)
                → Σ (Fin n → Fin n → Set) λ _R'_ 
                  → Σ (Preference n _R'_) 
                    λ p' → (∀ a   → ¬ a ≡ z → P p' z a)
                        × (∀ x y → ¬ x ≡ z → ¬ y ≡ z
                                  → (x R y → x R' y)
                                  × (x R' y → x R y))
  Alter-First {n = n} {_R_ = _R_} p z 
    = _R'_ , (p' , (λ {a ¬a≡z (z-first .a) → ¬a≡z Eq.refl
                    ; a ¬a≡z (original .a .z ¬z≡z _) → ¬z≡z Eq.refl}) 
                , agree-non-z) 
    where
      data _R'_ : Fin n → Fin n → Set where
        z-first  : ∀ a                     → z R' a
        original : ∀ a b → ¬ b ≡ z → a R b → a R' b
        
      R'-trans : ∀ a b c → a R' b → b R' c → a R' c
      R'-trans a b c (z-first .b) _ = z-first c
      R'-trans a b c (original .a .b ¬b≡b _) (z-first .c) = ⊥-elim (¬b≡b Eq.refl)
      R'-trans a b c (original .a .b ¬b≡z aRb) (original .b .c ¬c≡z bRc) 
        = original a c ¬c≡z (R-trans p a b c aRb bRc)

      R'-complete : ∀ a b → (a R' b) ⊎ (b R' a)
      R'-complete a b with a Fin.≟ z | b Fin.≟ z | R-complete p a b 
      ... | _ | false because ofⁿ ¬b≡z | inj₁ aRb 
        = inj₁ (original a b ¬b≡z aRb)
      ... | false because ofⁿ ¬a≡z | _ | inj₂ bRa 
        = inj₂ (original b a ¬a≡z bRa)
      ... | _ | true because ofʸ b≡z | _ rewrite b≡z = inj₂ (z-first a)
      ... | true because ofʸ a≡z | _ | _ rewrite a≡z = inj₁ (z-first b)
      
      R'-dec : ∀ a b → (a R' b) ⊎ ¬ (a R' b)
      R'-dec a b with a Fin.≟ z | b Fin.≟ z | R-dec p a b
      ... | true because ofʸ a≡z | _ | _ rewrite a≡z = inj₁ (z-first b) 
      ... | _ | false because ofⁿ ¬b≡z | inj₁ aRb = inj₁ (original a b ¬b≡z aRb)
      ... | false because ofⁿ ¬a≡z | true because ofʸ b≡z | _ = 
        inj₂ (λ {(z-first .b) → ¬a≡z Eq.refl
                ; (original .a .b ¬b≡z _) → ¬b≡z b≡z})
      ... | false because ofⁿ ¬a≡z | false because ofⁿ ¬b≡z | inj₂ bPa = 
        inj₂ (λ {(z-first .b) → ¬a≡z Eq.refl
                ; (original .a .b ¬b≡z aRb) → bPa aRb})

      p' : Preference n _R'_
      p' = record { 
          R-trans    = R'-trans 
        ; R-complete = R'-complete 
        ; R-dec      = R'-dec }
      
      agree-non-z : ∀ x y → (¬ x ≡ z) → (¬ y ≡ z) 
                  → (x R y → x R' y) × (x R' y → x R y)
      agree-non-z x y ¬x≡z ¬y≡z 
        = (λ {xRy → original x y ¬y≡z xRy})
        , (λ { (z-first .y) → ⊥-elim (¬x≡z Eq.refl)
            ; (original .x .y _ xRy) → xRy})

data Trivial {n : ℕ} : Fin n → Fin n → Set where
  tt : ∀ a b → Trivial a b

TrivialVoter : Preference n Trivial
TrivialVoter = record { R-trans = λ a b c _ _ → tt a c 
             ; R-complete = λ a b → inj₁ (tt a b)
             ; R-dec = λ a b → inj₁ (tt a b) } 