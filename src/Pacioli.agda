{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The Pacioli group and the mathematics of double-entry bookkeeping
--
-- This module formalises the construction behind double-entry
-- bookkeeping (DEB) as described in David Ellerman's "The Mathematics
-- of Double-Entry Bookkeeping" (Mathematics Magazine, 1985) and its
-- vector generalisation ("Double Entry Multidimensional Accounting",
-- 1986).
--
-- Ellerman's central observation: a T-account
--
--     [ debit // credit ]
--
-- is exactly an ordered pair in the *group of differences* of a
-- commutative monoid -- the additive analogue of building the
-- fractions q = num/den out of the whole numbers. The group of
-- differences of the non-negative reals (or, multidimensionally, the
-- non-negative vectors) is what he names the *Pacioli group*, after
-- Luca Pacioli who codified DEB in 1494. The modern relative of this
-- construction is the Grothendieck group; the Pacioli group is its
-- 15th-century special case.
--
-- The construction works for any *cancellative* commutative monoid.
-- Cancellativity is the algebraic content of "you can read a balance
-- off a T-account unambiguously": it is precisely what makes the
-- cross-sum equality below an equivalence relation. We therefore take
-- as input a commutative monoid together with a single left-
-- cancellation witness, and derive everything else.
------------------------------------------------------------------------

module Pacioli where

import Level as Level
open import Level using (Level; 0ℓ; _⊔_)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles using (CommutativeMonoid; AbelianGroup; Group)
open import Algebra.Structures using (IsAbelianGroup)
import Algebra.Definitions as Def
import Algebra.Construct.Pointwise as Pointwise
import Algebra.Construct.Sub.Group
import Algebra.Morphism.Structures as Morphism
import Algebra.Module.Bundles.Raw as ModuleRaw
import Algebra.Module.Morphism.Structures as ModuleMorphism
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; cong; cong₂)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
import Data.Nat.Base as ℕ
open import Data.Nat.Base using (ℕ)
import Data.Nat.Properties as ℕ
import Data.Parity.Base as ℙ
open import Data.Parity.Base using (Parity; 0ℙ; 1ℙ)
import Data.Integer.Base as ℤ
import Data.Integer.Properties as ℤ
import Data.Integer.Tactic.RingSolver as ℤRing
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Vec.Base as Vec
open import Data.Vec.Base using (Vec; []; _∷_)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Functional as V using (Vector; replicate)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_; proj₁; Σ-syntax)

private
  variable
    c ℓ ℓ≤ : Level

------------------------------------------------------------------------
-- T-accounts
--
-- A T-account is an ordered pair written [ debit // credit ]. The name
-- "T-account" comes from the bookkeeper's habit of drawing a T and
-- listing debit entries down the left, credit entries down the right.

record DebitCredit (A : Set c) : Set c where
  constructor _//_
  field
    debit  : A
    credit : A

open DebitCredit public

------------------------------------------------------------------------
-- The Pacioli group of a cancellative commutative monoid
--
-- Given a commutative monoid (Amounts, ∙, ε) in which ∙ is left-
-- cancellative, the T-accounts over it form an abelian group: the
-- group of differences, a.k.a. the Pacioli group.

module Pacioli
  {c ℓ} (CM : CommutativeMonoid c ℓ)  (open CommutativeMonoid CM)
  (∙-cancelˡ : Def.LeftCancellative _≈_ _∙_)
  where

  -- Pull in equational reasoning for the underlying setoid, and the two
  -- stdlib consequences we need: deriving right-cancellation from left-
  -- cancellation + commutativity, and the "middle-four exchange"
  -- (a ∙ c) ∙ (b ∙ d) ≈ (a ∙ b) ∙ (c ∙ d), which is the only shuffling
  -- lemma the group laws really require.
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Algebra.Consequences.Setoid setoid
    using (comm∧cancelˡ⇒cancelʳ; comm∧assoc⇒middleFour)

  ∙-cancelʳ : Def.RightCancellative _≈_ _∙_
  ∙-cancelʳ = comm∧cancelˡ⇒cancelʳ comm ∙-cancelˡ

  middleFour : ∀ a b c d → (a ∙ c) ∙ (b ∙ d) ≈ (a ∙ b) ∙ (c ∙ d)
  middleFour a b c d = comm∧assoc⇒middleFour ∙-cong comm assoc a c b d

  infix  4 _≈ᵀ_
  infixl 6 _∙ᵀ_
  infix  8 _⁻¹ᵀ

  -- Equality of T-accounts is equality of *cross-sums* (Ellerman):
  --   [ a // b ] = [ c // d ]   iff   a + d = c + b.
  -- Two accounts denote the same balance exactly when the debit of one
  -- plus the credit of the other agree both ways round.
  _≈ᵀ_ : Rel (DebitCredit Carrier) ℓ
  (a // b) ≈ᵀ (c // d) = a ∙ d ≈ c ∙ b

  -- Addition of T-accounts: add debits to debits, credits to credits.
  -- This is the *only* operation in the whole system. Posting a journal
  -- to a ledger, recording a transaction -- all of it is this ∙ᵀ.
  _∙ᵀ_ : Op₂ (DebitCredit Carrier)
  (a // b) ∙ᵀ (c // d) = (a ∙ c) // (b ∙ d)

  -- The zero-account [ ε // ε ]. Equations encode as zero-accounts and
  -- valid transactions are additions of (other) zero-accounts; zero
  -- plus zero is zero.
  εᵀ : DebitCredit Carrier
  εᵀ = ε // ε

  -- The additive inverse reverses debit and credit. Negating an account
  -- is just swapping the two sides of the T -- this is what makes a
  -- "credit" the undo of a "debit".
  _⁻¹ᵀ : Op₁ (DebitCredit Carrier)
  (a // b) ⁻¹ᵀ = b // a

  -- Polarity is the abstract debit/credit reading symmetry. Debit
  -- polarity leaves an account alone; credit polarity swaps the two
  -- sides, i.e. applies the group inverse.
  polarize : Parity → Op₁ (DebitCredit Carrier)
  polarize 0ℙ x = x
  polarize 1ℙ x = x ⁻¹ᵀ

  ----------------------------------------------------------------------
  -- The cross-sum relation is an equivalence.
  --
  -- Reflexivity and symmetry are immediate. Transitivity is the one
  -- place cancellation earns its keep: from a∙d ≈ c∙b and c∙f ≈ e∙d we
  -- recover a∙f ≈ e∙b only after cancelling the shared d.

  ≈ᵀ-refl : Reflexive _≈ᵀ_
  ≈ᵀ-refl {a // b} = refl

  ≈ᵀ-sym : Symmetric _≈ᵀ_
  ≈ᵀ-sym {a // b} {c // d} = sym

  -- A small rearrangement used three times below: (a ∙ b) ∙ c ≈ (a ∙ c) ∙ b.
  private
    swap : ∀ a b c → (a ∙ b) ∙ c ≈ (a ∙ c) ∙ b
    swap a b c = begin
      (a ∙ b) ∙ c  ≈⟨ assoc a b c ⟩
      a ∙ (b ∙ c)  ≈⟨ ∙-congˡ (comm b c) ⟩
      a ∙ (c ∙ b)  ≈⟨ assoc a c b ⟨
      (a ∙ c) ∙ b  ∎

  ≈ᵀ-trans : Transitive _≈ᵀ_
  ≈ᵀ-trans {a // b} {c // d} {e // f} ad≈cb cf≈ed =
    ∙-cancelʳ d (a ∙ f) (e ∙ b) (begin
      (a ∙ f) ∙ d  ≈⟨ swap a f d ⟩
      (a ∙ d) ∙ f  ≈⟨ ∙-congʳ ad≈cb ⟩
      (c ∙ b) ∙ f  ≈⟨ swap c b f ⟩
      (c ∙ f) ∙ b  ≈⟨ ∙-congʳ cf≈ed ⟩
      (e ∙ d) ∙ b  ≈⟨ swap e d b ⟩
      (e ∙ b) ∙ d  ∎)

  ≈ᵀ-isEquivalence : IsEquivalence _≈ᵀ_
  ≈ᵀ-isEquivalence = record
    { refl = ≈ᵀ-refl ; sym = ≈ᵀ-sym ; trans = ≈ᵀ-trans }

  ----------------------------------------------------------------------
  -- The group laws.
  --
  -- Each is a short reasoning chain; the middle-four exchange handles
  -- congruence and commutativity, and plain associativity/identity
  -- handle the rest. No solver required.

  ∙ᵀ-cong : ∀ {x y u v} → x ≈ᵀ y → u ≈ᵀ v → (x ∙ᵀ u) ≈ᵀ (y ∙ᵀ v)
  ∙ᵀ-cong {a // b} {a′ // b′} {c // d} {c′ // d′} p q = begin
    (a ∙ c) ∙ (b′ ∙ d′)  ≈⟨ middleFour a b′ c d′ ⟩
    (a ∙ b′) ∙ (c ∙ d′)  ≈⟨ ∙-cong p q ⟩
    (a′ ∙ b) ∙ (c′ ∙ d)  ≈⟨ middleFour a′ c′ b d ⟩
    (a′ ∙ c′) ∙ (b ∙ d)  ∎

  -- Associativity is *not* a commutative shuffle: both components are
  -- reassociated independently, so a single ∙-cong over the two sides
  -- does it.
  ∙ᵀ-assoc : ∀ x y z → ((x ∙ᵀ y) ∙ᵀ z) ≈ᵀ (x ∙ᵀ (y ∙ᵀ z))
  ∙ᵀ-assoc (a // b) (c // d) (e // f) =
    ∙-cong (assoc a c e) (sym (assoc b d f))

  ∙ᵀ-identityˡ : ∀ x → (εᵀ ∙ᵀ x) ≈ᵀ x
  ∙ᵀ-identityˡ (a // b) = begin
    (ε ∙ a) ∙ b  ≈⟨ ∙-congʳ (identityˡ a) ⟩
    a ∙ b        ≈⟨ ∙-congˡ (identityˡ b) ⟨
    a ∙ (ε ∙ b)  ∎

  ∙ᵀ-identityʳ : ∀ x → (x ∙ᵀ εᵀ) ≈ᵀ x
  ∙ᵀ-identityʳ (a // b) = begin
    (a ∙ ε) ∙ b  ≈⟨ ∙-congʳ (identityʳ a) ⟩
    a ∙ b        ≈⟨ ∙-congˡ (identityʳ b) ⟨
    a ∙ (b ∙ ε)  ∎

  -- The double-entry principle in one line: an account and its
  -- debit/credit-reversed inverse sum to the zero-account.
  ∙ᵀ-inverseˡ : ∀ x → ((x ⁻¹ᵀ) ∙ᵀ x) ≈ᵀ εᵀ
  ∙ᵀ-inverseˡ (a // b) = begin
    (b ∙ a) ∙ ε  ≈⟨ identityʳ _ ⟩
    b ∙ a        ≈⟨ comm b a ⟩
    a ∙ b        ≈⟨ identityˡ _ ⟨
    ε ∙ (a ∙ b)  ∎

  ∙ᵀ-inverseʳ : ∀ x → (x ∙ᵀ (x ⁻¹ᵀ)) ≈ᵀ εᵀ
  ∙ᵀ-inverseʳ (a // b) = begin
    (a ∙ b) ∙ ε  ≈⟨ identityʳ _ ⟩
    a ∙ b        ≈⟨ comm a b ⟩
    b ∙ a        ≈⟨ identityˡ _ ⟨
    ε ∙ (b ∙ a)  ∎

  ⁻¹ᵀ-cong : ∀ {x y} → x ≈ᵀ y → (x ⁻¹ᵀ) ≈ᵀ (y ⁻¹ᵀ)
  ⁻¹ᵀ-cong {a // b} {c // d} p = begin
    b ∙ c  ≈⟨ comm b c ⟩
    c ∙ b  ≈⟨ p ⟨
    a ∙ d  ≈⟨ comm a d ⟩
    d ∙ a  ∎

  ∙ᵀ-comm : ∀ x y → (x ∙ᵀ y) ≈ᵀ (y ∙ᵀ x)
  ∙ᵀ-comm (a // b) (c // d) = ∙-cong (comm a c) (comm d b)

  ----------------------------------------------------------------------
  -- Polarity acts on T-accounts by the two-element group.

  polarize-involutive : ∀ p x → polarize p (polarize p x) ≈ᵀ x
  polarize-involutive 0ℙ x        = ≈ᵀ-refl
  polarize-involutive 1ℙ (a // b) = ≈ᵀ-refl

  polarize-action : ∀ p q x → polarize (p ℙ.+ q) x ≈ᵀ polarize p (polarize q x)
  polarize-action 0ℙ q x        = ≈ᵀ-refl
  polarize-action 1ℙ 0ℙ x      = ≈ᵀ-refl
  polarize-action 1ℙ 1ℙ (a // b) = ≈ᵀ-refl

  polarize-hom : ∀ p x y → polarize p (x ∙ᵀ y) ≈ᵀ (polarize p x ∙ᵀ polarize p y)
  polarize-hom 0ℙ x y = ≈ᵀ-refl
  polarize-hom 1ℙ x y = ≈ᵀ-refl

  polarize-credit : ∀ x → polarize 1ℙ x ≈ᵀ (polarize 0ℙ x) ⁻¹ᵀ
  polarize-credit x = ≈ᵀ-refl

  ----------------------------------------------------------------------
  -- Assembling the abelian group.
  --
  -- This is the canonical stdlib shape: a tower of records whose leaves
  -- are the named proofs above, so the structure reads as a table of
  -- contents rather than a wall of inline proofs.

  isPacioliGroup : IsAbelianGroup _≈ᵀ_ _∙ᵀ_ εᵀ _⁻¹ᵀ
  isPacioliGroup = record
    { isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = ≈ᵀ-isEquivalence
            ; ∙-cong        = ∙ᵀ-cong
            }
          ; assoc = ∙ᵀ-assoc
          }
        ; identity = ∙ᵀ-identityˡ , ∙ᵀ-identityʳ
        }
      ; inverse = ∙ᵀ-inverseˡ , ∙ᵀ-inverseʳ
      ; ⁻¹-cong = ⁻¹ᵀ-cong
      }
    ; comm = ∙ᵀ-comm
    }

  PacioliGroup : AbelianGroup c ℓ
  PacioliGroup = record
    { Carrier = DebitCredit Carrier
    ; _≈_ = _≈ᵀ_
    ; _∙_ = _∙ᵀ_
    ; ε = εᵀ
    ; _⁻¹ = _⁻¹ᵀ
    ; isAbelianGroup = isPacioliGroup
    }

------------------------------------------------------------------------
-- Reduced representatives require more structure
--
-- The abstract Pacioli construction only needs cancellation. A canonical
-- reduced T-account needs a way to find a common part (meet) and remove
-- a proven subamount (difference). This tier captures exactly that
-- extra structure without baking it into the group completion.

record MeetDifferenceMonoid c ℓ ℓ≤ : Set (Level.suc (c ⊔ ℓ ⊔ ℓ≤)) where
  infix  4 _≤_
  infixl 6 _∸_
  infixl 7 _⊓_

  field
    Amounts : CommutativeMonoid c ℓ

  open CommutativeMonoid Amounts public

  field
    ∙-cancelˡ : Def.LeftCancellative _≈_ _∙_
    _≤_       : Rel Carrier ℓ≤
    _⊓_       : Op₂ Carrier
    _∸_       : Op₂ Carrier

    ⊓≤ˡ : ∀ a b → (a ⊓ b) ≤ a
    ⊓≤ʳ : ∀ a b → (a ⊓ b) ≤ b

    -- Removing a subamount and adding it back recovers the original.
    ∸-sound : ∀ {a k} → k ≤ a → (a ∸ k) ∙ k ≈ a

    -- After removing the meet, no common part remains.
    ∸-meet-zero : ∀ a b → ((a ∸ (a ⊓ b)) ⊓ (b ∸ (a ⊓ b))) ≈ ε

module ReducedPacioli {c ℓ ℓ≤} (MDM : MeetDifferenceMonoid c ℓ ℓ≤) where

  open MeetDifferenceMonoid MDM
  open import Relation.Binary.Reasoning.Setoid setoid

  module P = Pacioli Amounts ∙-cancelˡ

  T : Set c
  T = DebitCredit Carrier

  common : T → Carrier
  common (a // b) = a ⊓ b

  reduce : T → T
  reduce (a // b) =
    let k = a ⊓ b in
    (a ∸ k) // (b ∸ k)

  polarizedReduce : Parity → T → T
  polarizedReduce p x = reduce (P.polarize p x)

  polarizedReading : Parity → T → Carrier
  polarizedReading p x = debit (polarizedReduce p x)

  reduced-disjoint : ∀ x → (debit (reduce x) ⊓ credit (reduce x)) ≈ ε
  reduced-disjoint (a // b) = ∸-meet-zero a b

  polarizedReduce-disjoint : ∀ p x → (debit (polarizedReduce p x) ⊓ credit (polarizedReduce p x)) ≈ ε
  polarizedReduce-disjoint p x = reduced-disjoint (P.polarize p x)

  reduce-preserves : ∀ x → reduce x P.≈ᵀ x
  reduce-preserves (a // b) =
    let k = a ⊓ b
        a′ = a ∸ k
        b′ = b ∸ k
    in begin
      a′ ∙ b        ≈⟨ ∙-congˡ (sym (∸-sound (⊓≤ʳ a b))) ⟩
      a′ ∙ (b′ ∙ k) ≈⟨ ∙-congˡ (comm b′ k) ⟩
      a′ ∙ (k ∙ b′) ≈⟨ assoc a′ k b′ ⟨
      (a′ ∙ k) ∙ b′ ≈⟨ ∙-congʳ (∸-sound (⊓≤ˡ a b)) ⟩
      a ∙ b′        ∎

  polarizedReduce-preserves : ∀ p x → polarizedReduce p x P.≈ᵀ P.polarize p x
  polarizedReduce-preserves p x = reduce-preserves (P.polarize p x)

private
  ℕ-∸-⊓ : ∀ a b → a ℕ.∸ (a ℕ.⊓ b) ≡ a ℕ.∸ b
  ℕ-∸-⊓ a b with ℕ.≤-total a b
  ... | inj₁ a≤b
    rewrite ℕ.m≤n⇒m⊓n≡m a≤b
          | ℕ.n∸n≡0 a
          | ℕ.m≤n⇒m∸n≡0 a≤b = ≡-refl
  ... | inj₂ b≤a
    rewrite ℕ.m≥n⇒m⊓n≡n b≤a = ≡-refl

  ℕ-reduced-disjoint : ∀ a b → ((a ℕ.∸ (a ℕ.⊓ b)) ℕ.⊓ (b ℕ.∸ (a ℕ.⊓ b))) ≡ 0
  ℕ-reduced-disjoint a b with ℕ.≤-total a b
  ... | inj₁ a≤b
    rewrite ℕ.m≤n⇒m⊓n≡m a≤b
          | ℕ.n∸n≡0 a = ≡-refl
  ... | inj₂ b≤a
    rewrite ℕ.m≥n⇒m⊓n≡n b≤a
          | ℕ.n∸n≡0 b = ℕ.⊓-zeroʳ (a ℕ.∸ b)

ℕ-MeetDifferenceMonoid : MeetDifferenceMonoid 0ℓ 0ℓ 0ℓ
ℕ-MeetDifferenceMonoid = record
  { Amounts       = ℕ.+-0-commutativeMonoid
  ; ∙-cancelˡ     = ℕ.+-cancelˡ-≡
  ; _≤_           = ℕ._≤_
  ; _⊓_           = ℕ._⊓_
  ; _∸_           = ℕ._∸_
  ; ⊓≤ˡ           = ℕ.m⊓n≤m
  ; ⊓≤ʳ           = ℕ.m⊓n≤n
  ; ∸-sound       = ℕ.m∸n+n≡m
  ; ∸-meet-zero   = ℕ-reduced-disjoint
  }

module ScalarIntegerReading where

  module P = Pacioli ℕ.+-0-commutativeMonoid ℕ.+-cancelˡ-≡
  module R = ReducedPacioli ℕ-MeetDifferenceMonoid

  T : Set
  T = DebitCredit ℕ

  signedMagnitude : Parity → ℕ → ℤ.ℤ
  signedMagnitude p n = ℤ._◃_ (ℙ.toSign p) n

  toℤ : T → ℤ.ℤ
  toℤ x with ℕ.≤-total (debit x) (credit x)
  ... | inj₁ _ = signedMagnitude 1ℙ (R.polarizedReading 1ℙ x)
  ... | inj₂ _ = signedMagnitude 0ℙ (R.polarizedReading 0ℙ x)

  toℤ-⊖ : ∀ a b → toℤ (a // b) ≡ ℤ._⊖_ a b
  toℤ-⊖ a b with ℕ.≤-total a b
  ... | inj₁ a≤b = ≡-trans
    (cong (ℤ._◃_ (ℙ.toSign 1ℙ)) (ℕ-∸-⊓ b a))
    (≡-trans
      (ℤ.-◃n≡-n (b ℕ.∸ a))
      (≡-sym (ℤ.⊖-≤ a≤b)))
  ... | inj₂ b≤a = ≡-trans
    (cong (ℤ._◃_ (ℙ.toSign 0ℙ)) (ℕ-∸-⊓ a b))
    (≡-trans
      (ℤ.+◃n≡+n (a ℕ.∸ b))
      (≡-sym (ℤ.⊖-≥ b≤a)))

  toℤ-diff : ∀ a b → toℤ (a // b) ≡ (ℤ.+ a) ℤ.- (ℤ.+ b)
  toℤ-diff a b = ≡-trans (toℤ-⊖ a b) (≡-sym (ℤ.[+m]-[+n]≡m⊖n a b))

  integer-diff-homo : ∀ i j k l →
    (i ℤ.+ k) ℤ.- (j ℤ.+ l) ≡ ((i ℤ.- j) ℤ.+ (k ℤ.- l))
  integer-diff-homo = ℤRing.solve-∀

  nat-diff-homo : ∀ a b c d →
    (ℤ.+ (a ℕ.+ c)) ℤ.- (ℤ.+ (b ℕ.+ d))
      ≡ (((ℤ.+ a) ℤ.- (ℤ.+ b)) ℤ.+ ((ℤ.+ c) ℤ.- (ℤ.+ d)))
  nat-diff-homo a b c d = ≡-trans
    (cong₂ ℤ._-_ (ℤ.pos-+ a c) (ℤ.pos-+ b d))
    (integer-diff-homo (ℤ.+ a) (ℤ.+ b) (ℤ.+ c) (ℤ.+ d))

  toℤ-homo : ∀ x y → toℤ (x P.∙ᵀ y) ≡ toℤ x ℤ.+ toℤ y
  toℤ-homo (a // b) (c // d) = ≡-trans
    (toℤ-diff (a ℕ.+ c) (b ℕ.+ d))
    (≡-trans
      (nat-diff-homo a b c d)
      (cong₂ ℤ._+_ (≡-sym (toℤ-diff a b)) (≡-sym (toℤ-diff c d))))

  add-right-diff : ∀ a b k →
    (ℤ.+ (a ℕ.+ k)) ℤ.- (ℤ.+ (b ℕ.+ k)) ≡ (ℤ.+ a) ℤ.- (ℤ.+ b)
  add-right-diff a b k = ≡-trans
    (ℤ.[+m]-[+n]≡m⊖n (a ℕ.+ k) (b ℕ.+ k))
    (≡-trans
      (cong₂ ℤ._⊖_ (ℕ.+-comm a k) (ℕ.+-comm b k))
      (≡-trans
        (ℤ.+-cancelˡ-⊖ k a b)
        (≡-sym (ℤ.[+m]-[+n]≡m⊖n a b))))

  cross-diff : ∀ a b c d →
    a ℕ.+ d ≡ c ℕ.+ b →
    (ℤ.+ a) ℤ.- (ℤ.+ b) ≡ (ℤ.+ c) ℤ.- (ℤ.+ d)
  cross-diff a b c d p = ≡-trans
    (≡-sym (add-right-diff a b d))
    (≡-trans
      (cong₂ ℤ._-_ (cong ℤ.+_ p) (cong ℤ.+_ (ℕ.+-comm b d)))
      (add-right-diff c d b))

  toℤ-cong : ∀ x y → x P.≈ᵀ y → toℤ x ≡ toℤ y
  toℤ-cong (a // b) (c // d) p = ≡-trans
    (toℤ-diff a b)
    (≡-trans
      (cross-diff a b c d p)
      (≡-sym (toℤ-diff c d)))

  toℤ-ε : toℤ P.εᵀ ≡ ℤ.0ℤ
  toℤ-ε = ≡-trans (toℤ-⊖ 0 0) (ℤ.n⊖n≡0 0)

  toℤ-inverse : ∀ x → toℤ (x P.⁻¹ᵀ) ≡ ℤ.-_ (toℤ x)
  toℤ-inverse (a // b) = ≡-trans
    (toℤ-⊖ b a)
    (≡-trans
      (ℤ.⊖-swap b a)
      (cong ℤ.-_ (≡-sym (toℤ-⊖ a b))))

  module ToℤGroup = Morphism.GroupMorphisms
    (AbelianGroup.rawGroup P.PacioliGroup)
    (AbelianGroup.rawGroup ℤ.+-0-abelianGroup)

  isToℤGroupHomomorphism : ToℤGroup.IsGroupHomomorphism toℤ
  isToℤGroupHomomorphism = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ {x} {y} → toℤ-cong x y }
        ; homo = toℤ-homo
        }
      ; ε-homo = toℤ-ε
      }
    ; ⁻¹-homo = toℤ-inverse
    }

  fromℤ : ℤ.ℤ → T
  fromℤ (ℤ.+ n)      = n // 0
  fromℤ ℤ.-[1+ n ] = 0 // ℕ.suc n

  toℤ-fromℤ : ∀ i → toℤ (fromℤ i) ≡ i
  toℤ-fromℤ (ℤ.+ n)      = toℤ-⊖ n 0
  toℤ-fromℤ ℤ.-[1+ n ] = toℤ-⊖ 0 (ℕ.suc n)

  integer-diff-crossˡ : ∀ i j l → (i ℤ.- j) ℤ.+ (j ℤ.+ l) ≡ i ℤ.+ l
  integer-diff-crossˡ = ℤRing.solve-∀

  integer-diff-crossʳ : ∀ k l j → (k ℤ.- l) ℤ.+ (j ℤ.+ l) ≡ k ℤ.+ j
  integer-diff-crossʳ = ℤRing.solve-∀

  integer-diff-cross : ∀ i j k l →
    i ℤ.- j ≡ k ℤ.- l → i ℤ.+ l ≡ k ℤ.+ j
  integer-diff-cross i j k l p = ≡-trans
    (≡-sym (integer-diff-crossˡ i j l))
    (≡-trans
      (cong (λ x → x ℤ.+ (j ℤ.+ l)) p)
      (integer-diff-crossʳ k l j))

  nat-diff-cross : ∀ a b c d →
    (ℤ.+ a) ℤ.- (ℤ.+ b) ≡ (ℤ.+ c) ℤ.- (ℤ.+ d) →
    a ℕ.+ d ≡ c ℕ.+ b
  nat-diff-cross a b c d p = ℤ.+-injective (≡-trans
    (ℤ.pos-+ a d)
    (≡-trans
      (integer-diff-cross (ℤ.+ a) (ℤ.+ b) (ℤ.+ c) (ℤ.+ d) p)
      (≡-sym (ℤ.pos-+ c b))))

  toℤ-injective : ∀ x y → toℤ x ≡ toℤ y → x P.≈ᵀ y
  toℤ-injective (a // b) (c // d) p = nat-diff-cross a b c d (≡-trans
    (≡-sym (toℤ-diff a b))
    (≡-trans p (toℤ-diff c d)))

  toℤ-surjective : ∀ i → Σ[ x ∈ T ] (∀ {z} → z P.≈ᵀ x → toℤ z ≡ i)
  toℤ-surjective i = fromℤ i , λ {z} z≈fromℤᵢ → ≡-trans
    (toℤ-cong z (fromℤ i) z≈fromℤᵢ)
    (toℤ-fromℤ i)

  isToℤGroupIsomorphism : ToℤGroup.IsGroupIsomorphism toℤ
  isToℤGroupIsomorphism = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isToℤGroupHomomorphism
      ; injective = λ {x} {y} → toℤ-injective x y
      }
    ; surjective = toℤ-surjective
    }

------------------------------------------------------------------------
-- The non-negative n-vectors as a cancellative commutative monoid
--
-- Ellerman's multidimensional accounting: amounts are vectors of
-- incommensurate non-negative quantities (so many dollars, so many
-- euros, so many tonnes of steel), added componentwise. ℕ is a
-- cancellative commutative monoid under +, and that property is
-- inherited componentwise by Vec.

module NonNegativeVectors (m : ℕ) where

  Amount : Set
  Amount = Vec ℕ m

  infixl 6 _+_
  _+_ : Op₂ Amount
  _+_ = Vec.zipWith ℕ._+_

  -- Vec-of-(commutative monoid) is a commutative monoid, built from the
  -- componentwise lifting lemmas in Data.Vec.Properties.
  Amounts : CommutativeMonoid 0ℓ 0ℓ
  Amounts = record
    { Carrier = Amount
    ; _≈_ = _≡_
    ; _∙_ = _+_
    ; ε   = Vec.replicate m 0
    ; isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = record
                { refl = ≡-refl
                ; sym = ≡-sym
                ; trans = ≡-trans
                }
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = Vecₚ.zipWith-assoc ℕ.+-assoc
            }
          ; identity =
              Vecₚ.zipWith-identityˡ ℕ.+-identityˡ
            , Vecₚ.zipWith-identityʳ ℕ.+-identityʳ
          }
        ; comm = Vecₚ.zipWith-comm ℕ.+-comm
        }
    }

  -- Left-cancellation, componentwise. Right-cancellation is then free
  -- inside the Pacioli construction (derived from this + commutativity),
  -- so we never write it out.
  +-cancelˡ′ : ∀ {m} → Def.LeftCancellative (_≡_ {A = Vec ℕ m}) (Vec.zipWith ℕ._+_)
  +-cancelˡ′ []       []       []       _  = ≡-refl
  +-cancelˡ′ (x ∷ xs) (y ∷ ys) (z ∷ zs) eq =
    cong₂ _∷_ (ℕ.+-cancelˡ-≡ x y z (cong Vec.head eq))
              (+-cancelˡ′ xs ys zs (cong Vec.tail eq))

  +-cancelˡ : Def.LeftCancellative _≡_ _+_
  +-cancelˡ = +-cancelˡ′

module VectorIntegerReading (m : ℕ) where

  module N = NonNegativeVectors m
  module P = Pacioli N.Amounts N.+-cancelˡ
  module S = ScalarIntegerReading

  T : Set
  T = DebitCredit N.Amount

  IntVector : Set
  IntVector = Vector ℤ.ℤ m

  IntVectorGroup : AbelianGroup 0ℓ 0ℓ
  IntVectorGroup = Pointwise.abelianGroup (Fin m) ℤ.+-0-abelianGroup

  toℤᵛ : T → IntVector
  toℤᵛ (a // b) i = S.toℤ (Vec.lookup a i // Vec.lookup b i)

  toℤᵛ-cong : ∀ x y → x P.≈ᵀ y → ∀ i → toℤᵛ x i ≡ toℤᵛ y i
  toℤᵛ-cong (a // b) (c // d) p i = S.toℤ-cong
    (Vec.lookup a i // Vec.lookup b i)
    (Vec.lookup c i // Vec.lookup d i)
    (≡-trans
      (≡-sym (Vecₚ.lookup-zipWith ℕ._+_ i a d))
      (≡-trans
        (cong (λ xs → Vec.lookup xs i) p)
        (Vecₚ.lookup-zipWith ℕ._+_ i c b)))

  toℤᵛ-homo : ∀ x y → ∀ i → toℤᵛ (x P.∙ᵀ y) i ≡ toℤᵛ x i ℤ.+ toℤᵛ y i
  toℤᵛ-homo (a // b) (c // d) i = ≡-trans
    (cong₂ (λ x y → S.toℤ (x // y))
      (Vecₚ.lookup-zipWith ℕ._+_ i a c)
      (Vecₚ.lookup-zipWith ℕ._+_ i b d))
    (S.toℤ-homo (Vec.lookup a i // Vec.lookup b i)
                 (Vec.lookup c i // Vec.lookup d i))

  toℤᵛ-ε : ∀ i → toℤᵛ P.εᵀ i ≡ ℤ.0ℤ
  toℤᵛ-ε i = ≡-trans
    (cong₂ (λ x y → S.toℤ (x // y))
      (Vecₚ.lookup-replicate i 0)
      (Vecₚ.lookup-replicate i 0))
    S.toℤ-ε

  toℤᵛ-inverse : ∀ x → ∀ i → toℤᵛ (x P.⁻¹ᵀ) i ≡ ℤ.-_ (toℤᵛ x i)
  toℤᵛ-inverse (a // b) i = S.toℤ-inverse (Vec.lookup a i // Vec.lookup b i)

  module ToℤᵛGroup = Morphism.GroupMorphisms
    (AbelianGroup.rawGroup P.PacioliGroup)
    (AbelianGroup.rawGroup IntVectorGroup)

  isToℤᵛGroupHomomorphism : ToℤᵛGroup.IsGroupHomomorphism toℤᵛ
  isToℤᵛGroupHomomorphism = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ {x} {y} → toℤᵛ-cong x y }
        ; homo = toℤᵛ-homo
        }
      ; ε-homo = toℤᵛ-ε
      }
    ; ⁻¹-homo = toℤᵛ-inverse
    }

  fromℤᵛ : IntVector → T
  fromℤᵛ v =
    Vec.tabulate (λ i → debit (S.fromℤ (v i))) //
    Vec.tabulate (λ i → credit (S.fromℤ (v i)))

  toℤᵛ-fromℤᵛ : ∀ v i → toℤᵛ (fromℤᵛ v) i ≡ v i
  toℤᵛ-fromℤᵛ v i = ≡-trans
    (cong₂ (λ x y → S.toℤ (x // y))
      (Vecₚ.lookup∘tabulate (λ j → debit (S.fromℤ (v j))) i)
      (Vecₚ.lookup∘tabulate (λ j → credit (S.fromℤ (v j))) i))
    (S.toℤ-fromℤ (v i))

  lookup-ext : ∀ {xs ys : Vec ℕ m} →
    (∀ i → Vec.lookup xs i ≡ Vec.lookup ys i) → xs ≡ ys
  lookup-ext {xs = xs} {ys = ys} p = ≡-trans
    (≡-sym (Vecₚ.tabulate∘lookup xs))
    (≡-trans (Vecₚ.tabulate-cong p) (Vecₚ.tabulate∘lookup ys))

  toℤᵛ-injective : ∀ x y → (∀ i → toℤᵛ x i ≡ toℤᵛ y i) → x P.≈ᵀ y
  toℤᵛ-injective (a // b) (c // d) p = lookup-ext λ i → ≡-trans
    (Vecₚ.lookup-zipWith ℕ._+_ i a d)
    (≡-trans
      (S.toℤ-injective
        (Vec.lookup a i // Vec.lookup b i)
        (Vec.lookup c i // Vec.lookup d i)
        (p i))
      (≡-sym (Vecₚ.lookup-zipWith ℕ._+_ i c b)))

  toℤᵛ-surjective :
    ∀ v → Σ[ x ∈ T ] (∀ {z} → z P.≈ᵀ x → ∀ i → toℤᵛ z i ≡ v i)
  toℤᵛ-surjective v = fromℤᵛ v , λ {z} z≈fromℤᵛv i → ≡-trans
    (toℤᵛ-cong z (fromℤᵛ v) z≈fromℤᵛv i)
    (toℤᵛ-fromℤᵛ v i)

  isToℤᵛGroupIsomorphism : ToℤᵛGroup.IsGroupIsomorphism toℤᵛ
  isToℤᵛGroupIsomorphism = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isToℤᵛGroupHomomorphism
      ; injective = λ {x} {y} → toℤᵛ-injective x y
      }
    ; surjective = toℤᵛ-surjective
    }

  dot : ∀ {n} → Vector ℤ.ℤ n → Vector ℤ.ℤ n → ℤ.ℤ
  dot {ℕ.zero}  prices position = ℤ.0ℤ
  dot {ℕ.suc n} prices position =
    prices zero ℤ.* position zero ℤ.+ dot (V.tail prices) (V.tail position)

  dot-congʳ : ∀ {n : ℕ} (prices : Vector ℤ.ℤ n) {position position′ : Vector ℤ.ℤ n} →
    (∀ i → position i ≡ position′ i) → dot prices position ≡ dot prices position′
  dot-congʳ {ℕ.zero}  prices position≈position′ = ≡-refl
  dot-congʳ {ℕ.suc n} prices position≈position′ =
    cong₂ ℤ._+_
      (cong (prices zero ℤ.*_) (position≈position′ zero))
      (dot-congʳ (V.tail prices) (λ i → position≈position′ (suc i)))

  dot-distribʳ-step : ∀ a b c d e →
    a ℤ.* (b ℤ.+ c) ℤ.+ (d ℤ.+ e)
      ≡ (a ℤ.* b ℤ.+ d) ℤ.+ (a ℤ.* c ℤ.+ e)
  dot-distribʳ-step = ℤRing.solve-∀

  dot-distribʳ : ∀ {n : ℕ} (prices position position′ : Vector ℤ.ℤ n) →
    dot prices (λ i → position i ℤ.+ position′ i)
      ≡ dot prices position ℤ.+ dot prices position′
  dot-distribʳ {ℕ.zero}  prices position position′ = ≡-sym (ℤ.+-identityʳ ℤ.0ℤ)
  dot-distribʳ {ℕ.suc n} prices position position′ = ≡-trans
    (cong (λ x → prices zero ℤ.* (position zero ℤ.+ position′ zero) ℤ.+ x)
      (dot-distribʳ (V.tail prices) (V.tail position) (V.tail position′)))
    (dot-distribʳ-step
      (prices zero) (position zero) (position′ zero)
      (dot (V.tail prices) (V.tail position))
      (dot (V.tail prices) (V.tail position′)))

  dot-zeroʳ : ∀ {n : ℕ} (prices : Vector ℤ.ℤ n) →
    dot prices (λ _ → ℤ.0ℤ) ≡ ℤ.0ℤ
  dot-zeroʳ {ℕ.zero}  prices = ≡-refl
  dot-zeroʳ {ℕ.suc n} prices = ≡-trans
    (cong₂ ℤ._+_
      (ℤ.*-zeroʳ (prices zero))
      (dot-zeroʳ (V.tail prices)))
    (ℤ.+-identityʳ ℤ.0ℤ)

  dot-negʳ-step : ∀ a b d → a ℤ.* (ℤ.- b) ℤ.+ (ℤ.- d) ≡ ℤ.- (a ℤ.* b ℤ.+ d)
  dot-negʳ-step = ℤRing.solve-∀

  dot-negʳ : ∀ {n : ℕ} (prices position : Vector ℤ.ℤ n) →
    dot prices (λ i → ℤ.-_ (position i)) ≡ ℤ.-_ (dot prices position)
  dot-negʳ {ℕ.zero}  prices position = ≡-refl
  dot-negʳ {ℕ.suc n} prices position = ≡-trans
    (cong (λ x → prices zero ℤ.* (ℤ.- position zero) ℤ.+ x)
      (dot-negʳ (V.tail prices) (V.tail position)))
    (dot-negʳ-step
      (prices zero) (position zero)
      (dot (V.tail prices) (V.tail position)))

  valuation : IntVector → T → ℤ.ℤ
  valuation prices account = dot prices (toℤᵛ account)

  valuation-cong : ∀ prices x y → x P.≈ᵀ y → valuation prices x ≡ valuation prices y
  valuation-cong prices x y x≈y = dot-congʳ prices (toℤᵛ-cong x y x≈y)

  valuation-homo : ∀ prices x y →
    valuation prices (x P.∙ᵀ y) ≡ valuation prices x ℤ.+ valuation prices y
  valuation-homo prices x y = ≡-trans
    (dot-congʳ prices (toℤᵛ-homo x y))
    (dot-distribʳ prices (toℤᵛ x) (toℤᵛ y))

  valuation-ε : ∀ prices → valuation prices P.εᵀ ≡ ℤ.0ℤ
  valuation-ε prices = ≡-trans
    (dot-congʳ prices toℤᵛ-ε)
    (dot-zeroʳ prices)

  valuation-inverse : ∀ prices x →
    valuation prices (x P.⁻¹ᵀ) ≡ ℤ.-_ (valuation prices x)
  valuation-inverse prices x = ≡-trans
    (dot-congʳ prices (toℤᵛ-inverse x))
    (dot-negʳ prices (toℤᵛ x))

  valuation-fromℤᵛ : ∀ prices position →
    valuation prices (fromℤᵛ position) ≡ dot prices position
  valuation-fromℤᵛ prices position = dot-congʳ prices (toℤᵛ-fromℤᵛ position)

  module ValuationGroup (prices : IntVector) = Morphism.GroupMorphisms
    (AbelianGroup.rawGroup P.PacioliGroup)
    (AbelianGroup.rawGroup ℤ.+-0-abelianGroup)

  isValuationGroupHomomorphism :
    ∀ prices → ValuationGroup.IsGroupHomomorphism prices (valuation prices)
  isValuationGroupHomomorphism prices = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ {x} {y} → valuation-cong prices x y }
        ; homo = valuation-homo prices
        }
      ; ε-homo = valuation-ε prices
      }
    ; ⁻¹-homo = valuation-inverse prices
    }

  dot-congˡ : ∀ {n : ℕ} {prices prices′ : Vector ℤ.ℤ n} (position : Vector ℤ.ℤ n) →
    (∀ i → prices i ≡ prices′ i) → dot prices position ≡ dot prices′ position
  dot-congˡ {ℕ.zero}  position prices≈prices′ = ≡-refl
  dot-congˡ {ℕ.suc n} position prices≈prices′ =
    cong₂ ℤ._+_
      (cong (λ x → x ℤ.* position zero) (prices≈prices′ zero))
      (dot-congˡ (V.tail position) (λ i → prices≈prices′ (suc i)))

  dot-distribˡ-step : ∀ a b c d e →
    (a ℤ.+ b) ℤ.* c ℤ.+ (d ℤ.+ e)
      ≡ (a ℤ.* c ℤ.+ d) ℤ.+ (b ℤ.* c ℤ.+ e)
  dot-distribˡ-step = ℤRing.solve-∀

  dot-distribˡ : ∀ {n : ℕ} (prices prices′ position : Vector ℤ.ℤ n) →
    dot (λ i → prices i ℤ.+ prices′ i) position
      ≡ dot prices position ℤ.+ dot prices′ position
  dot-distribˡ {ℕ.zero}  prices prices′ position = ≡-sym (ℤ.+-identityʳ ℤ.0ℤ)
  dot-distribˡ {ℕ.suc n} prices prices′ position = ≡-trans
    (cong (λ x → (prices zero ℤ.+ prices′ zero) ℤ.* position zero ℤ.+ x)
      (dot-distribˡ (V.tail prices) (V.tail prices′) (V.tail position)))
    (dot-distribˡ-step
      (prices zero) (prices′ zero) (position zero)
      (dot (V.tail prices) (V.tail position))
      (dot (V.tail prices′) (V.tail position)))

  dot-zeroˡ : ∀ {n : ℕ} (position : Vector ℤ.ℤ n) →
    dot (λ _ → ℤ.0ℤ) position ≡ ℤ.0ℤ
  dot-zeroˡ {ℕ.zero}  position = ≡-refl
  dot-zeroˡ {ℕ.suc n} position = ≡-trans
    (cong₂ ℤ._+_
      (ℤ.*-zeroˡ (position zero))
      (dot-zeroˡ (V.tail position)))
    (ℤ.+-identityʳ ℤ.0ℤ)

  dot-negˡ-step : ∀ a b d → (ℤ.- a) ℤ.* b ℤ.+ (ℤ.- d) ≡ ℤ.- (a ℤ.* b ℤ.+ d)
  dot-negˡ-step = ℤRing.solve-∀

  dot-negˡ : ∀ {n : ℕ} (prices position : Vector ℤ.ℤ n) →
    dot (λ i → ℤ.-_ (prices i)) position ≡ ℤ.-_ (dot prices position)
  dot-negˡ {ℕ.zero}  prices position = ≡-refl
  dot-negˡ {ℕ.suc n} prices position = ≡-trans
    (cong (λ x → (ℤ.- prices zero) ℤ.* position zero ℤ.+ x)
      (dot-negˡ (V.tail prices) (V.tail position)))
    (dot-negˡ-step
      (prices zero) (position zero)
      (dot (V.tail prices) (V.tail position)))

  ValuationFunctional : Set
  ValuationFunctional = T → ℤ.ℤ

  ValuationFunctionalGroup : AbelianGroup 0ℓ 0ℓ
  ValuationFunctionalGroup = Pointwise.abelianGroup T ℤ.+-0-abelianGroup

  pricesToValuation : IntVector → ValuationFunctional
  pricesToValuation = valuation

  pricesToValuation-cong :
    ∀ prices prices′ → (∀ i → prices i ≡ prices′ i) →
    ∀ account → pricesToValuation prices account ≡ pricesToValuation prices′ account
  pricesToValuation-cong prices prices′ prices≈prices′ account =
    dot-congˡ (toℤᵛ account) prices≈prices′

  pricesToValuation-homo :
    ∀ prices prices′ account →
    pricesToValuation (λ i → prices i ℤ.+ prices′ i) account
      ≡ pricesToValuation prices account ℤ.+ pricesToValuation prices′ account
  pricesToValuation-homo prices prices′ account =
    dot-distribˡ prices prices′ (toℤᵛ account)

  pricesToValuation-ε :
    ∀ account → pricesToValuation (λ _ → ℤ.0ℤ) account ≡ ℤ.0ℤ
  pricesToValuation-ε account = dot-zeroˡ (toℤᵛ account)

  pricesToValuation-inverse :
    ∀ prices account →
    pricesToValuation (λ i → ℤ.-_ (prices i)) account
      ≡ ℤ.-_ (pricesToValuation prices account)
  pricesToValuation-inverse prices account =
    dot-negˡ prices (toℤᵛ account)

  module PricesToValuationGroup = Morphism.GroupMorphisms
    (AbelianGroup.rawGroup IntVectorGroup)
    (AbelianGroup.rawGroup ValuationFunctionalGroup)

  isPricesToValuationGroupHomomorphism :
    PricesToValuationGroup.IsGroupHomomorphism pricesToValuation
  isPricesToValuationGroupHomomorphism = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record
          { cong = λ {prices} {prices′} → pricesToValuation-cong prices prices′ }
        ; homo = pricesToValuation-homo
        }
      ; ε-homo = pricesToValuation-ε
      }
    ; ⁻¹-homo = pricesToValuation-inverse
    }

  scalePosition : ℤ.ℤ → IntVector → IntVector
  scalePosition k position i = k ℤ.* position i

  scaleAccount : ℤ.ℤ → T → T
  scaleAccount k account = fromℤᵛ (scalePosition k (toℤᵛ account))

  scaleAccount-reading : ∀ k account i →
    toℤᵛ (scaleAccount k account) i ≡ k ℤ.* toℤᵛ account i
  scaleAccount-reading k account i =
    toℤᵛ-fromℤᵛ (scalePosition k (toℤᵛ account)) i

  AccountRawModule : ModuleRaw.RawModule ℤ.ℤ 0ℓ 0ℓ
  AccountRawModule = record
    { Carrierᴹ = T
    ; _≈ᴹ_ = P._≈ᵀ_
    ; _+ᴹ_ = P._∙ᵀ_
    ; _*ₗ_ = scaleAccount
    ; _*ᵣ_ = λ account k → scaleAccount k account
    ; 0ᴹ = P.εᵀ
    ; -ᴹ_ = P._⁻¹ᵀ
    }

  record IntegerAction {v ℓv : Level} (A : AbelianGroup v ℓv) : Set (v ⊔ ℓv) where
    infixl 7 _⋆_
    open AbelianGroup A renaming
      ( Carrier to Value ; _≈_ to _≈ᴬ_ ; _∙_ to _+ᴬ_
      ; ε to 0ᴬ ; _⁻¹ to -ᴬ_
      )
    field
      _⋆_ : ℤ.ℤ → Value → Value

      ⋆-congʳ : ∀ i {x y} → x ≈ᴬ y → i ⋆ x ≈ᴬ i ⋆ y
      ⋆-homo-+ : ∀ i j x → ((i ℤ.+ j) ⋆ x) ≈ᴬ (i ⋆ x) +ᴬ (j ⋆ x)
      ⋆-zeroˡ : ∀ x → ℤ.0ℤ ⋆ x ≈ᴬ 0ᴬ
      ⋆-identityˡ : ∀ x → ℤ.1ℤ ⋆ x ≈ᴬ x
      ⋆-assoc : ∀ i j x → ((i ℤ.* j) ⋆ x) ≈ᴬ (i ⋆ (j ⋆ x))
      ⋆-negˡ : ∀ i x → (ℤ.- i) ⋆ x ≈ᴬ -ᴬ (i ⋆ x)

      ⋆-distribʳ : ∀ i x y → (i ⋆ (x +ᴬ y)) ≈ᴬ (i ⋆ x) +ᴬ (i ⋆ y)
      ⋆-zeroʳ : ∀ i → i ⋆ 0ᴬ ≈ᴬ 0ᴬ
      ⋆-negʳ : ∀ i x → i ⋆ (-ᴬ x) ≈ᴬ -ᴬ (i ⋆ x)

  module GeneralValuation {v ℓv : Level}
    (A : AbelianGroup v ℓv)
    (action : IntegerAction A)
    where

    open AbelianGroup A renaming
      ( Carrier to Value ; _≈_ to _≈ᴬ_ ; _∙_ to _+ᴬ_
      ; ε to 0ᴬ ; _⁻¹ to -ᴬ_
      ; ∙-cong to +ᴬ-cong ; ∙-congˡ to +ᴬ-congˡ ; ∙-congʳ to +ᴬ-congʳ
      ; identityʳ to +ᴬ-identityʳ
      ; assoc to +ᴬ-assoc ; comm to +ᴬ-comm
      ; refl to reflᴬ ; sym to symᴬ ; trans to transᴬ
      ; reflexive to reflexiveᴬ
      )
    open IntegerAction action
    open import Relation.Binary.Reasoning.Setoid setoid
    open import Algebra.Consequences.Setoid setoid
      using (comm∧assoc⇒middleFour)
    open import Algebra.Properties.AbelianGroup A
      using (⁻¹-∙-comm; ε⁻¹≈ε)

    ValueVector : Set v
    ValueVector = Vector Value m

    ValueVectorGroup : AbelianGroup v ℓv
    ValueVectorGroup = Pointwise.abelianGroup (Fin m) A

    ValuationᴬFunctional : Set v
    ValuationᴬFunctional = T → Value

    ValuationᴬFunctionalGroup : AbelianGroup v ℓv
    ValuationᴬFunctionalGroup = Pointwise.abelianGroup T A

    ValueRawModule : ModuleRaw.RawModule ℤ.ℤ v ℓv
    ValueRawModule = record
      { Carrierᴹ = Value
      ; _≈ᴹ_ = _≈ᴬ_
      ; _+ᴹ_ = _+ᴬ_
      ; _*ₗ_ = λ k x → k ⋆ x
      ; _*ᵣ_ = λ x k → k ⋆ x
      ; 0ᴹ = 0ᴬ
      ; -ᴹ_ = -ᴬ_
      }

    ValueVectorRawModule : ModuleRaw.RawModule ℤ.ℤ v ℓv
    ValueVectorRawModule = record
      { Carrierᴹ = ValueVector
      ; _≈ᴹ_ = λ prices prices′ → ∀ i → prices i ≈ᴬ prices′ i
      ; _+ᴹ_ = λ prices prices′ i → prices i +ᴬ prices′ i
      ; _*ₗ_ = λ k prices i → k ⋆ prices i
      ; _*ᵣ_ = λ prices k i → k ⋆ prices i
      ; 0ᴹ = λ _ → 0ᴬ
      ; -ᴹ_ = λ prices i → -ᴬ (prices i)
      }

    ValuationᴬFunctionalRawModule : ModuleRaw.RawModule ℤ.ℤ v ℓv
    ValuationᴬFunctionalRawModule = record
      { Carrierᴹ = ValuationᴬFunctional
      ; _≈ᴹ_ = λ f g → ∀ account → f account ≈ᴬ g account
      ; _+ᴹ_ = λ f g account → f account +ᴬ g account
      ; _*ₗ_ = λ k f account → k ⋆ f account
      ; _*ᵣ_ = λ f k account → k ⋆ f account
      ; 0ᴹ = λ _ → 0ᴬ
      ; -ᴹ_ = λ f account → -ᴬ (f account)
      }

    middleFourᴬ : ∀ a b c d →
      (a +ᴬ b) +ᴬ (c +ᴬ d) ≈ᴬ (a +ᴬ c) +ᴬ (b +ᴬ d)
    middleFourᴬ =
      comm∧assoc⇒middleFour +ᴬ-cong +ᴬ-comm +ᴬ-assoc

    dotᴬ : ∀ {n : ℕ} → Vector Value n → Vector ℤ.ℤ n → Value
    dotᴬ {ℕ.zero}  prices position = 0ᴬ
    dotᴬ {ℕ.suc n} prices position =
      (position zero ⋆ prices zero) +ᴬ dotᴬ (V.tail prices) (V.tail position)

    dotᴬ-congʳ : ∀ {n : ℕ} (prices : Vector Value n) {position position′ : Vector ℤ.ℤ n} →
      (∀ i → position i ≡ position′ i) → dotᴬ prices position ≈ᴬ dotᴬ prices position′
    dotᴬ-congʳ {ℕ.zero}  prices position≈position′ = reflᴬ
    dotᴬ-congʳ {ℕ.suc n} prices position≈position′ =
      +ᴬ-cong
        (reflexiveᴬ (cong (λ q → q ⋆ prices zero) (position≈position′ zero)))
        (dotᴬ-congʳ (V.tail prices) (λ i → position≈position′ (suc i)))

    dotᴬ-distribʳ-step : ∀ i j price d e →
      ((i ℤ.+ j) ⋆ price) +ᴬ (d +ᴬ e)
        ≈ᴬ ((i ⋆ price) +ᴬ d) +ᴬ ((j ⋆ price) +ᴬ e)
    dotᴬ-distribʳ-step i j price d e = begin
      ((i ℤ.+ j) ⋆ price) +ᴬ (d +ᴬ e)
        ≈⟨ +ᴬ-congʳ (⋆-homo-+ i j price) ⟩
      ((i ⋆ price) +ᴬ (j ⋆ price)) +ᴬ (d +ᴬ e)
        ≈⟨ middleFourᴬ (i ⋆ price) (j ⋆ price) d e ⟩
      ((i ⋆ price) +ᴬ d) +ᴬ ((j ⋆ price) +ᴬ e) ∎

    dotᴬ-distribʳ : ∀ {n : ℕ} (prices : Vector Value n) (position position′ : Vector ℤ.ℤ n) →
      dotᴬ prices (λ i → position i ℤ.+ position′ i)
        ≈ᴬ dotᴬ prices position +ᴬ dotᴬ prices position′
    dotᴬ-distribʳ {ℕ.zero}  prices position position′ = symᴬ (+ᴬ-identityʳ 0ᴬ)
    dotᴬ-distribʳ {ℕ.suc n} prices position position′ = begin
      (position zero ℤ.+ position′ zero) ⋆ prices zero
        +ᴬ dotᴬ (V.tail prices) (λ i → V.tail position i ℤ.+ V.tail position′ i)
        ≈⟨ +ᴬ-congˡ
             (dotᴬ-distribʳ (V.tail prices) (V.tail position) (V.tail position′)) ⟩
      (position zero ℤ.+ position′ zero) ⋆ prices zero
        +ᴬ (dotᴬ (V.tail prices) (V.tail position)
          +ᴬ dotᴬ (V.tail prices) (V.tail position′))
        ≈⟨ dotᴬ-distribʳ-step
             (position zero) (position′ zero) (prices zero)
             (dotᴬ (V.tail prices) (V.tail position))
             (dotᴬ (V.tail prices) (V.tail position′)) ⟩
      dotᴬ prices position +ᴬ dotᴬ prices position′ ∎

    dotᴬ-zeroʳ : ∀ {n : ℕ} (prices : Vector Value n) →
      dotᴬ prices (λ _ → ℤ.0ℤ) ≈ᴬ 0ᴬ
    dotᴬ-zeroʳ {ℕ.zero}  prices = reflᴬ
    dotᴬ-zeroʳ {ℕ.suc n} prices = begin
      (ℤ.0ℤ ⋆ prices zero) +ᴬ dotᴬ (V.tail prices) (λ _ → ℤ.0ℤ)
        ≈⟨ +ᴬ-cong (⋆-zeroˡ (prices zero)) (dotᴬ-zeroʳ (V.tail prices)) ⟩
      0ᴬ +ᴬ 0ᴬ
        ≈⟨ +ᴬ-identityʳ 0ᴬ ⟩
      0ᴬ ∎

    dotᴬ-negʳ-step : ∀ i price d →
      ((ℤ.- i) ⋆ price) +ᴬ -ᴬ d ≈ᴬ -ᴬ ((i ⋆ price) +ᴬ d)
    dotᴬ-negʳ-step i price d = begin
      ((ℤ.- i) ⋆ price) +ᴬ -ᴬ d
        ≈⟨ +ᴬ-congʳ (⋆-negˡ i price) ⟩
      -ᴬ (i ⋆ price) +ᴬ -ᴬ d
        ≈⟨ ⁻¹-∙-comm (i ⋆ price) d ⟩
      -ᴬ ((i ⋆ price) +ᴬ d) ∎

    dotᴬ-negʳ : ∀ {n : ℕ} (prices : Vector Value n) (position : Vector ℤ.ℤ n) →
      dotᴬ prices (λ i → ℤ.-_ (position i)) ≈ᴬ -ᴬ (dotᴬ prices position)
    dotᴬ-negʳ {ℕ.zero}  prices position = symᴬ ε⁻¹≈ε
    dotᴬ-negʳ {ℕ.suc n} prices position = begin
      ℤ.- position zero ⋆ prices zero
        +ᴬ dotᴬ (V.tail prices) (λ i → ℤ.- V.tail position i)
        ≈⟨ +ᴬ-congˡ (dotᴬ-negʳ (V.tail prices) (V.tail position)) ⟩
      ℤ.- position zero ⋆ prices zero
        +ᴬ -ᴬ dotᴬ (V.tail prices) (V.tail position)
        ≈⟨ dotᴬ-negʳ-step
             (position zero) (prices zero)
             (dotᴬ (V.tail prices) (V.tail position)) ⟩
      -ᴬ dotᴬ prices position ∎

    dotᴬ-congˡ : ∀ {n : ℕ} {prices prices′ : Vector Value n} (position : Vector ℤ.ℤ n) →
      (∀ i → prices i ≈ᴬ prices′ i) → dotᴬ prices position ≈ᴬ dotᴬ prices′ position
    dotᴬ-congˡ {ℕ.zero}  position prices≈prices′ = reflᴬ
    dotᴬ-congˡ {ℕ.suc n} position prices≈prices′ =
      +ᴬ-cong
        (⋆-congʳ (position zero) (prices≈prices′ zero))
        (dotᴬ-congˡ (V.tail position) (λ i → prices≈prices′ (suc i)))

    dotᴬ-distribˡ-step : ∀ i price price′ d e →
      (i ⋆ (price +ᴬ price′)) +ᴬ (d +ᴬ e)
        ≈ᴬ ((i ⋆ price) +ᴬ d) +ᴬ ((i ⋆ price′) +ᴬ e)
    dotᴬ-distribˡ-step i price price′ d e = begin
      (i ⋆ (price +ᴬ price′)) +ᴬ (d +ᴬ e)
        ≈⟨ +ᴬ-congʳ (⋆-distribʳ i price price′) ⟩
      ((i ⋆ price) +ᴬ (i ⋆ price′)) +ᴬ (d +ᴬ e)
        ≈⟨ middleFourᴬ (i ⋆ price) (i ⋆ price′) d e ⟩
      ((i ⋆ price) +ᴬ d) +ᴬ ((i ⋆ price′) +ᴬ e) ∎

    dotᴬ-distribˡ : ∀ {n : ℕ} (prices prices′ : Vector Value n) (position : Vector ℤ.ℤ n) →
      dotᴬ (λ i → prices i +ᴬ prices′ i) position
        ≈ᴬ dotᴬ prices position +ᴬ dotᴬ prices′ position
    dotᴬ-distribˡ {ℕ.zero}  prices prices′ position = symᴬ (+ᴬ-identityʳ 0ᴬ)
    dotᴬ-distribˡ {ℕ.suc n} prices prices′ position = begin
      position zero ⋆ (prices zero +ᴬ prices′ zero)
        +ᴬ dotᴬ (λ i → V.tail prices i +ᴬ V.tail prices′ i) (V.tail position)
        ≈⟨ +ᴬ-congˡ
             (dotᴬ-distribˡ (V.tail prices) (V.tail prices′) (V.tail position)) ⟩
      position zero ⋆ (prices zero +ᴬ prices′ zero)
        +ᴬ (dotᴬ (V.tail prices) (V.tail position)
          +ᴬ dotᴬ (V.tail prices′) (V.tail position))
        ≈⟨ dotᴬ-distribˡ-step
             (position zero) (prices zero) (prices′ zero)
             (dotᴬ (V.tail prices) (V.tail position))
             (dotᴬ (V.tail prices′) (V.tail position)) ⟩
      dotᴬ prices position +ᴬ dotᴬ prices′ position ∎

    dotᴬ-zeroˡ : ∀ {n : ℕ} (position : Vector ℤ.ℤ n) →
      dotᴬ (λ _ → 0ᴬ) position ≈ᴬ 0ᴬ
    dotᴬ-zeroˡ {ℕ.zero}  position = reflᴬ
    dotᴬ-zeroˡ {ℕ.suc n} position = begin
      (position zero ⋆ 0ᴬ) +ᴬ dotᴬ (λ _ → 0ᴬ) (V.tail position)
        ≈⟨ +ᴬ-cong (⋆-zeroʳ (position zero)) (dotᴬ-zeroˡ (V.tail position)) ⟩
      0ᴬ +ᴬ 0ᴬ
        ≈⟨ +ᴬ-identityʳ 0ᴬ ⟩
      0ᴬ ∎

    dotᴬ-negˡ-step : ∀ i price d →
      (i ⋆ (-ᴬ price)) +ᴬ -ᴬ d ≈ᴬ -ᴬ ((i ⋆ price) +ᴬ d)
    dotᴬ-negˡ-step i price d = begin
      (i ⋆ (-ᴬ price)) +ᴬ -ᴬ d
        ≈⟨ +ᴬ-congʳ (⋆-negʳ i price) ⟩
      -ᴬ (i ⋆ price) +ᴬ -ᴬ d
        ≈⟨ ⁻¹-∙-comm (i ⋆ price) d ⟩
      -ᴬ ((i ⋆ price) +ᴬ d) ∎

    dotᴬ-negˡ : ∀ {n : ℕ} (prices : Vector Value n) (position : Vector ℤ.ℤ n) →
      dotᴬ (λ i → -ᴬ (prices i)) position ≈ᴬ -ᴬ (dotᴬ prices position)
    dotᴬ-negˡ {ℕ.zero}  prices position = symᴬ ε⁻¹≈ε
    dotᴬ-negˡ {ℕ.suc n} prices position = begin
      position zero ⋆ -ᴬ prices zero
        +ᴬ dotᴬ (λ i → -ᴬ V.tail prices i) (V.tail position)
        ≈⟨ +ᴬ-congˡ (dotᴬ-negˡ (V.tail prices) (V.tail position)) ⟩
      position zero ⋆ -ᴬ prices zero
        +ᴬ -ᴬ dotᴬ (V.tail prices) (V.tail position)
        ≈⟨ dotᴬ-negˡ-step
             (position zero) (prices zero)
             (dotᴬ (V.tail prices) (V.tail position)) ⟩
      -ᴬ dotᴬ prices position ∎

    dotᴬ-scaleʳ : ∀ {n : ℕ} k (prices : Vector Value n) (position : Vector ℤ.ℤ n) →
      dotᴬ prices (λ i → k ℤ.* position i) ≈ᴬ (k ⋆ dotᴬ prices position)
    dotᴬ-scaleʳ {ℕ.zero}  k prices position = symᴬ (⋆-zeroʳ k)
    dotᴬ-scaleʳ {ℕ.suc n} k prices position = begin
      (k ℤ.* position zero) ⋆ prices zero
        +ᴬ dotᴬ (V.tail prices) (λ i → k ℤ.* V.tail position i)
        ≈⟨ +ᴬ-cong
             (⋆-assoc k (position zero) (prices zero))
             (dotᴬ-scaleʳ k (V.tail prices) (V.tail position)) ⟩
      k ⋆ (position zero ⋆ prices zero)
        +ᴬ (k ⋆ dotᴬ (V.tail prices) (V.tail position))
        ≈⟨ symᴬ (⋆-distribʳ k (position zero ⋆ prices zero)
             (dotᴬ (V.tail prices) (V.tail position))) ⟩
      k ⋆ dotᴬ prices position ∎

    ⋆-commute : ∀ k q price → q ⋆ (k ⋆ price) ≈ᴬ (k ⋆ (q ⋆ price))
    ⋆-commute k q price = transᴬ
      (symᴬ (⋆-assoc q k price))
      (transᴬ
        (reflexiveᴬ (cong (λ r → r ⋆ price) (ℤ.*-comm q k)))
        (⋆-assoc k q price))

    dotᴬ-scaleˡ : ∀ {n : ℕ} k (prices : Vector Value n) (position : Vector ℤ.ℤ n) →
      dotᴬ (λ i → k ⋆ prices i) position ≈ᴬ (k ⋆ dotᴬ prices position)
    dotᴬ-scaleˡ {ℕ.zero}  k prices position = symᴬ (⋆-zeroʳ k)
    dotᴬ-scaleˡ {ℕ.suc n} k prices position = begin
      position zero ⋆ (k ⋆ prices zero)
        +ᴬ dotᴬ (λ i → k ⋆ V.tail prices i) (V.tail position)
        ≈⟨ +ᴬ-cong
             (⋆-commute k (position zero) (prices zero))
             (dotᴬ-scaleˡ k (V.tail prices) (V.tail position)) ⟩
      k ⋆ (position zero ⋆ prices zero)
        +ᴬ (k ⋆ dotᴬ (V.tail prices) (V.tail position))
        ≈⟨ symᴬ (⋆-distribʳ k (position zero ⋆ prices zero)
             (dotᴬ (V.tail prices) (V.tail position))) ⟩
      k ⋆ dotᴬ prices position ∎

    valuationᴬ : ValueVector → T → Value
    valuationᴬ prices account = dotᴬ prices (toℤᵛ account)

    valuationᴬ-cong : ∀ prices x y → x P.≈ᵀ y → valuationᴬ prices x ≈ᴬ valuationᴬ prices y
    valuationᴬ-cong prices x y x≈y = dotᴬ-congʳ prices (toℤᵛ-cong x y x≈y)

    valuationᴬ-homo : ∀ prices x y →
      valuationᴬ prices (x P.∙ᵀ y) ≈ᴬ valuationᴬ prices x +ᴬ valuationᴬ prices y
    valuationᴬ-homo prices x y = transᴬ
      (dotᴬ-congʳ prices (toℤᵛ-homo x y))
      (dotᴬ-distribʳ prices (toℤᵛ x) (toℤᵛ y))

    valuationᴬ-ε : ∀ prices → valuationᴬ prices P.εᵀ ≈ᴬ 0ᴬ
    valuationᴬ-ε prices = transᴬ
      (dotᴬ-congʳ prices toℤᵛ-ε)
      (dotᴬ-zeroʳ prices)

    valuationᴬ-inverse : ∀ prices x →
      valuationᴬ prices (x P.⁻¹ᵀ) ≈ᴬ -ᴬ (valuationᴬ prices x)
    valuationᴬ-inverse prices x = transᴬ
      (dotᴬ-congʳ prices (toℤᵛ-inverse x))
      (dotᴬ-negʳ prices (toℤᵛ x))

    module ValuationᴬGroup (prices : ValueVector) = Morphism.GroupMorphisms
      (AbelianGroup.rawGroup P.PacioliGroup)
      (AbelianGroup.rawGroup A)

    isValuationᴬGroupHomomorphism :
      ∀ prices → ValuationᴬGroup.IsGroupHomomorphism prices (valuationᴬ prices)
    isValuationᴬGroupHomomorphism prices = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = λ {x} {y} → valuationᴬ-cong prices x y }
          ; homo = valuationᴬ-homo prices
          }
        ; ε-homo = valuationᴬ-ε prices
        }
      ; ⁻¹-homo = valuationᴬ-inverse prices
      }

    valuationᴬ-*ₗ-homo : ∀ prices k account →
      valuationᴬ prices (scaleAccount k account) ≈ᴬ (k ⋆ valuationᴬ prices account)
    valuationᴬ-*ₗ-homo prices k account = transᴬ
      (dotᴬ-congʳ prices (scaleAccount-reading k account))
      (dotᴬ-scaleʳ k prices (toℤᵛ account))

    valuationᴬ-*ᵣ-homo : ∀ prices k account →
      valuationᴬ prices (scaleAccount k account) ≈ᴬ (k ⋆ valuationᴬ prices account)
    valuationᴬ-*ᵣ-homo = valuationᴬ-*ₗ-homo

    module ValuationᴬModule = ModuleMorphism.ModuleMorphisms
      AccountRawModule
      ValueRawModule

    isValuationᴬModuleHomomorphism :
      ∀ prices → ValuationᴬModule.IsModuleHomomorphism (valuationᴬ prices)
    isValuationᴬModuleHomomorphism prices = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = isValuationᴬGroupHomomorphism prices
        ; *ₗ-homo = valuationᴬ-*ₗ-homo prices
        ; *ᵣ-homo = valuationᴬ-*ᵣ-homo prices
        }
      }

    pricesToValuationᴬ : ValueVector → ValuationᴬFunctional
    pricesToValuationᴬ = valuationᴬ

    pricesToValuationᴬ-cong :
      ∀ prices prices′ → (∀ i → prices i ≈ᴬ prices′ i) →
      ∀ account → pricesToValuationᴬ prices account ≈ᴬ pricesToValuationᴬ prices′ account
    pricesToValuationᴬ-cong prices prices′ prices≈prices′ account =
      dotᴬ-congˡ (toℤᵛ account) prices≈prices′

    pricesToValuationᴬ-homo :
      ∀ prices prices′ account →
      pricesToValuationᴬ (λ i → prices i +ᴬ prices′ i) account
        ≈ᴬ pricesToValuationᴬ prices account +ᴬ pricesToValuationᴬ prices′ account
    pricesToValuationᴬ-homo prices prices′ account =
      dotᴬ-distribˡ prices prices′ (toℤᵛ account)

    pricesToValuationᴬ-ε :
      ∀ account → pricesToValuationᴬ (λ _ → 0ᴬ) account ≈ᴬ 0ᴬ
    pricesToValuationᴬ-ε account = dotᴬ-zeroˡ (toℤᵛ account)

    pricesToValuationᴬ-inverse :
      ∀ prices account →
      pricesToValuationᴬ (λ i → -ᴬ (prices i)) account
        ≈ᴬ -ᴬ (pricesToValuationᴬ prices account)
    pricesToValuationᴬ-inverse prices account =
      dotᴬ-negˡ prices (toℤᵛ account)

    module PricesToValuationᴬGroup = Morphism.GroupMorphisms
      (AbelianGroup.rawGroup ValueVectorGroup)
      (AbelianGroup.rawGroup ValuationᴬFunctionalGroup)

    isPricesToValuationᴬGroupHomomorphism :
      PricesToValuationᴬGroup.IsGroupHomomorphism pricesToValuationᴬ
    isPricesToValuationᴬGroupHomomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record
            { cong = λ {prices} {prices′} → pricesToValuationᴬ-cong prices prices′ }
          ; homo = pricesToValuationᴬ-homo
          }
        ; ε-homo = pricesToValuationᴬ-ε
        }
      ; ⁻¹-homo = pricesToValuationᴬ-inverse
      }

    pricesToValuationᴬ-*ₗ-homo : ∀ k prices account →
      pricesToValuationᴬ (λ i → k ⋆ prices i) account
        ≈ᴬ (k ⋆ pricesToValuationᴬ prices account)
    pricesToValuationᴬ-*ₗ-homo k prices account =
      dotᴬ-scaleˡ k prices (toℤᵛ account)

    pricesToValuationᴬ-*ᵣ-homo : ∀ k prices account →
      pricesToValuationᴬ (λ i → k ⋆ prices i) account
        ≈ᴬ (k ⋆ pricesToValuationᴬ prices account)
    pricesToValuationᴬ-*ᵣ-homo = pricesToValuationᴬ-*ₗ-homo

    module PricesToValuationᴬModule = ModuleMorphism.ModuleMorphisms
      ValueVectorRawModule
      ValuationᴬFunctionalRawModule

    isPricesToValuationᴬModuleHomomorphism :
      PricesToValuationᴬModule.IsModuleHomomorphism pricesToValuationᴬ
    isPricesToValuationᴬModuleHomomorphism = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = isPricesToValuationᴬGroupHomomorphism
        ; *ₗ-homo = pricesToValuationᴬ-*ₗ-homo
        ; *ᵣ-homo = pricesToValuationᴬ-*ᵣ-homo
        }
      }

  ℤ⋆-homo-+ : ∀ i j x → (i ℤ.+ j) ℤ.* x ≡ i ℤ.* x ℤ.+ j ℤ.* x
  ℤ⋆-homo-+ = ℤRing.solve-∀

  ℤ⋆-assoc : ∀ i j x → (i ℤ.* j) ℤ.* x ≡ i ℤ.* (j ℤ.* x)
  ℤ⋆-assoc = ℤ.*-assoc

  ℤ⋆-negˡ : ∀ i x → (ℤ.- i) ℤ.* x ≡ ℤ.- (i ℤ.* x)
  ℤ⋆-negˡ = ℤRing.solve-∀

  ℤ⋆-distribʳ : ∀ i x y → i ℤ.* (x ℤ.+ y) ≡ i ℤ.* x ℤ.+ i ℤ.* y
  ℤ⋆-distribʳ = ℤRing.solve-∀

  ℤ⋆-negʳ : ∀ i x → i ℤ.* (ℤ.- x) ≡ ℤ.- (i ℤ.* x)
  ℤ⋆-negʳ = ℤRing.solve-∀

  ℤIntegerAction : IntegerAction ℤ.+-0-abelianGroup
  ℤIntegerAction = record
    { _⋆_ = ℤ._*_
    ; ⋆-congʳ = λ i → cong (i ℤ.*_)
    ; ⋆-homo-+ = ℤ⋆-homo-+
    ; ⋆-zeroˡ = ℤ.*-zeroˡ
    ; ⋆-identityˡ = ℤ.*-identityˡ
    ; ⋆-assoc = ℤ⋆-assoc
    ; ⋆-negˡ = ℤ⋆-negˡ
    ; ⋆-distribʳ = ℤ⋆-distribʳ
    ; ⋆-zeroʳ = ℤ.*-zeroʳ
    ; ⋆-negʳ = ℤ⋆-negʳ
    }

  module ℤValuation = GeneralValuation ℤ.+-0-abelianGroup ℤIntegerAction

  dotᴬ≡dot : ∀ {n : ℕ} (prices position : Vector ℤ.ℤ n) →
    ℤValuation.dotᴬ prices position ≡ dot prices position
  dotᴬ≡dot {ℕ.zero}  prices position = ≡-refl
  dotᴬ≡dot {ℕ.suc n} prices position =
    cong₂ ℤ._+_
      (ℤ.*-comm (position zero) (prices zero))
      (dotᴬ≡dot (V.tail prices) (V.tail position))

  valuationᴬ≡valuation : ∀ prices account →
    ℤValuation.valuationᴬ prices account ≡ valuation prices account
  valuationᴬ≡valuation prices account =
    dotᴬ≡dot prices (toℤᵛ account)

------------------------------------------------------------------------
-- Accounting: rows, the trial balance, and balanced transactions
--
-- The bookkeeping vocabulary lines up with the algebra:
--   * a row / journal entry / ledger = one T-account per named account,
--     i.e. an element of the n-fold product of the Pacioli group
--   * the trial balance              = the group sum of a row (stdlib's
--                                      finite summation over a monoid)
--   * a balanced row / transaction   = a row whose trial balance is εᵀ
--
-- The balanced rows are exactly the kernel of the trial balance, and the
-- kernel of a group homomorphism is a subgroup. So "the initial ledger
-- balances" and "posting a balanced row keeps it balanced" are not
-- invariants we maintain -- they are closure of that subgroup, free.

module Accounting (m n : ℕ) where

  open NonNegativeVectors m using (Amounts; +-cancelˡ)
  open CommutativeMonoid Amounts using () renaming (ε to 𝟘)

  Amount : Set
  Amount = NonNegativeVectors.Amount m

  -- The Pacioli group of T-accounts over these amounts. We work inside
  -- it directly, so ∙ᵀ, εᵀ, the group laws and its equational reasoning
  -- are all in scope under their group names.
  module P = Pacioli Amounts +-cancelˡ
  open AbelianGroup P.PacioliGroup
    renaming (Carrier to T; _≈_ to _≈ᵀ_; _∙_ to _∙ᵀ_; ε to εᵀ; _⁻¹ to _⁻¹ᵀ)
  open import Relation.Binary.Reasoning.Setoid setoid

  -- Finite summation over the Pacioli group -- the trial balance -- and
  -- its distributivity over account-wise addition, both straight from
  -- the standard library's summation-over-a-(commutative-)monoid.
  open import Algebra.Properties.CommutativeMonoid.Sum commutativeMonoid
    using (sum; ∑-distrib-+)
  open import Algebra.Properties.AbelianGroup P.PacioliGroup
    using (⁻¹-∙-comm; ε⁻¹≈ε)

  -- A row assigns a T-account to each of the n named accounts. The rows
  -- are the n-fold product of the Pacioli group -- an abelian group under
  -- account-wise operations -- which the stdlib hands us for free as the
  -- pointwise lifting of the Pacioli group over the index set Fin n.
  RowGroup : AbelianGroup 0ℓ 0ℓ
  RowGroup = Pointwise.abelianGroup (Fin n) P.PacioliGroup

  open AbelianGroup RowGroup using () renaming
    ( Carrier to Row ; _≈_ to _≈ᴿ_ ; _∙_ to _∙ᴿ_
    ; ε to εᴿ ; _⁻¹ to _⁻¹ᴿ ; refl to reflᴿ )

  -- The trial balance of a row: sum its T-accounts in the Pacioli group.
  total : Row → T
  total f = sum f

  -- A row balances when its trial balance is the zero-account -- the
  -- double-entry principle. The balanced rows are exactly ker total.
  Balanced : Row → Set
  Balanced f = total f ≈ᵀ εᵀ

  Tx : Set
  Tx = Σ[ f ∈ Row ] Balanced f

  ----------------------------------------------------------------------
  -- ker total is a subgroup: it contains the zero row and is closed
  -- under account-wise addition. So the initial ledger balances and
  -- posting stays balanced -- closure, not per-post bookkeeping.

  -- The trial balance of the all-zero row is εᵀ (a sum of zeroes). The
  -- size is explicit because `replicate` discards it, so leaving it
  -- implicit would strand `sum`'s size as an unsolved metavariable.
  total-ε : ∀ k → sum {k} (replicate k εᵀ) ≈ᵀ εᵀ
  total-ε ℕ.zero    = refl
  total-ε (ℕ.suc k) = trans (identityˡ _) (total-ε k)

  -- The empty / initial ledger: every account at the zero-account.
  empty : Tx
  empty = εᴿ , total-ε n

  -- Posting two balanced rows: add account-wise. Balance is preserved by
  -- ∑-distrib-+ (total is a homomorphism) -- "zero ∙ᵀ zero is zero".
  post : Tx → Tx → Tx
  post (f , bf) (g , bg) = (f ∙ᴿ g) , (begin
    total (f ∙ᴿ g)      ≈⟨ ∑-distrib-+ f g ⟩
    total f ∙ᵀ total g  ≈⟨ ∙-cong bf bg ⟩
    εᵀ ∙ᵀ εᵀ            ≈⟨ identityˡ εᵀ ⟩
    εᵀ                  ∎)

  ----------------------------------------------------------------------
  -- A single posting: the row that is the T-account `v` at account `i`
  -- and the zero-account everywhere else. Its trial balance is just `v`.

  δ : ∀ {k} → Fin k → T → Vector T k
  δ zero    v = v V.∷ replicate _ εᵀ
  δ (suc i) v = εᵀ V.∷ δ i v

  total-δ : ∀ {k} (i : Fin k) v → sum (δ i v) ≈ᵀ v
  total-δ {ℕ.suc k} zero    v = trans (∙-congˡ (total-ε k)) (identityʳ v)
  total-δ           (suc i) v = trans (identityˡ _) (total-δ i v)

  ----------------------------------------------------------------------
  -- The fundamental transaction: move an amount between two accounts by
  -- debiting one and crediting the other. The debit posting [ a // 𝟘 ]
  -- and the credit posting [ 𝟘 // a ] are *inverse* T-accounts, so the
  -- row balances: the double-entry principle is literally x ∙ᵀ x⁻¹ᵀ.

  swapRow : Amount → Fin n → Fin n → Row
  swapRow a debitAcct creditAcct =
    δ debitAcct (a // 𝟘) ∙ᴿ δ creditAcct (𝟘 // a)

  swapBalanced : ∀ a d c → Balanced (swapRow a d c)
  swapBalanced a d c = begin
    total (δ d (a // 𝟘) ∙ᴿ δ c (𝟘 // a))         ≈⟨ ∑-distrib-+ (δ d (a // 𝟘)) (δ c (𝟘 // a)) ⟩
    total (δ d (a // 𝟘)) ∙ᵀ total (δ c (𝟘 // a))  ≈⟨ ∙-cong (total-δ d (a // 𝟘)) (total-δ c (𝟘 // a)) ⟩
    (a // 𝟘) ∙ᵀ (𝟘 // a)                          ≈⟨ inverseʳ (a // 𝟘) ⟩
    εᵀ                                             ∎

  swap : Amount → Fin n → Fin n → Tx
  swap a d c = swapRow a d c , swapBalanced a d c

  ----------------------------------------------------------------------
  -- Reversing a transaction: negate every account. This needs that the
  -- trial balance commutes with inversion -- total is a *group* homo,
  -- not merely a monoid one -- which is what upgrades ker total from
  -- "closed under ∙ᴿ" to a genuine subgroup.

  total-⁻¹ : ∀ {k} (f : Vector T k) → sum (λ i → f i ⁻¹ᵀ) ≈ᵀ (sum f) ⁻¹ᵀ
  total-⁻¹ {ℕ.zero}  f = sym ε⁻¹≈ε
  total-⁻¹ {ℕ.suc k} f =
    trans (∙-congˡ (total-⁻¹ (V.tail f)))
          (⁻¹-∙-comm (V.head f) (sum (V.tail f)))

  reverse : Tx → Tx
  reverse (f , bf) = (f ⁻¹ᴿ) , (begin
    total (f ⁻¹ᴿ)  ≈⟨ total-⁻¹ f ⟩
    (total f) ⁻¹ᵀ  ≈⟨ ⁻¹-cong bf ⟩
    εᵀ ⁻¹ᵀ         ≈⟨ ε⁻¹≈ε ⟩
    εᵀ             ∎)

  ----------------------------------------------------------------------
  -- Balanced transactions as a subgroup.
  --
  -- empty / post / reverse are the identity, multiplication and inverse
  -- of the balanced rows under account-wise operations. Presenting them
  -- through the stdlib's Subgroup -- the kernel of the trial balance
  -- total : RowGroup ⟶ PacioliGroup, given as the injection
  -- proj₁ : Tx ↪ Row -- pulls back all the group laws. Because the
  -- subgroup's equality *is* equality of the underlying rows, the
  -- monomorphism witness is pure refl / identity: the closure proofs
  -- (empty, post, reverse) are the only real content, exactly as it
  -- should be.

  module Sub = Algebra.Construct.Sub.Group (AbelianGroup.group RowGroup)

  balancedSubgroup : Sub.Subgroup 0ℓ 0ℓ
  balancedSubgroup = record
    { domain = record
        { Carrier = Tx
        ; _≈_     = λ x y → proj₁ x ≈ᴿ proj₁ y
        ; _∙_     = post
        ; ε       = empty
        ; _⁻¹     = reverse
        }
    ; ι = proj₁
    ; ι-monomorphism = record
        { isGroupHomomorphism = record
            { isMonoidHomomorphism = record
                { isMagmaHomomorphism = record
                    { isRelHomomorphism = record { cong = λ p → p }
                    ; homo = λ _ _ → reflᴿ
                    }
                ; ε-homo = reflᴿ
                }
            ; ⁻¹-homo = λ _ → reflᴿ
            }
        ; injective = λ p → p
        }
    }

  -- ...and so the balanced transactions are a group in their own right.
  TxGroup : Group 0ℓ 0ℓ
  TxGroup = Sub.Subgroup.group balancedSubgroup

------------------------------------------------------------------------
-- SPSC ring buffers as bounded T-accounts
--
-- The specification is deliberately just two monotone counters and two
-- bounds. The Pacioli account below is the accounting model of those
-- counters, not the admission controller: enqueue/dequeue constructors
-- require the non-negativity guards, and the verified layer packages
-- the usual empty-plus-preservation closure proof.

module RingBuffer (N : ℕ) where

  record State : Set where
    constructor ring
    field
      head : ℕ
      tail : ℕ

  open State public

  -- Freestanding specification: occupancy is head - tail and free space
  -- is (tail + N) - head. Safety is exactly the two halfspace guards.
  Occupancy : State → ℕ
  Occupancy s = head s ℕ.∸ tail s

  Free : State → ℕ
  Free s = (tail s ℕ.+ N) ℕ.∸ head s

  NoUnderflow : State → Set
  NoUnderflow s = tail s ℕ.≤ head s

  NoOverflow : State → Set
  NoOverflow s = head s ℕ.≤ tail s ℕ.+ N

  HasRoom : State → Set
  HasRoom s = head s ℕ.< tail s ℕ.+ N

  HasItem : State → Set
  HasItem s = tail s ℕ.< head s

  record Safe (s : State) : Set where
    constructor safe
    field
      noUnderflow : NoUnderflow s
      noOverflow  : NoOverflow s

  open Safe public

  emptyState : State
  emptyState = ring 0 0

  enqueue : (s : State) → HasRoom s → State
  enqueue s _ = ring (ℕ.suc (head s)) (tail s)

  dequeue : (s : State) → HasItem s → State
  dequeue s _ = ring (head s) (ℕ.suc (tail s))

  emptySafe : Safe emptyState
  emptySafe = safe ℕ.z≤n ℕ.z≤n

  enqueueSafe : ∀ s → Safe s → (room : HasRoom s) → Safe (enqueue s room)
  enqueueSafe s ok room = safe
    (ℕ.m≤n⇒m≤1+n (noUnderflow ok))
    room

  dequeueSafe : ∀ s → Safe s → (item : HasItem s) → Safe (dequeue s item)
  dequeueSafe s ok item = safe
    item
    (ℕ.m≤n⇒m≤1+n (noOverflow ok))

  ----------------------------------------------------------------------
  -- Accounting model.
  --
  -- Over ℕ, the Pacioli group is the group of differences of the two
  -- counters: [ head // tail ]. Posting one enqueue debits the head
  -- counter; posting one dequeue credits the tail counter.

  module P = Pacioli ℕ.+-0-commutativeMonoid ℕ.+-cancelˡ-≡
  open AbelianGroup P.PacioliGroup
    renaming (Carrier to T; _≈_ to _≈ᵀ_; _∙_ to _∙ᵀ_; ε to εᵀ; _⁻¹ to _⁻¹ᵀ)

  account : State → T
  account s = head s // tail s

  capacityAccount : State → T
  capacityAccount s = head s // (tail s ℕ.+ N)

  module R = ReducedPacioli ℕ-MeetDifferenceMonoid

  reducedAccount : State → T
  reducedAccount s = R.reduce (account s)

  reducedAccountPreserves : ∀ s → reducedAccount s ≈ᵀ account s
  reducedAccountPreserves s = R.reduce-preserves (account s)

  reducedAccountDisjoint : ∀ s → (debit (reducedAccount s) ℕ.⊓ credit (reducedAccount s)) ≡ 0
  reducedAccountDisjoint s = R.reduced-disjoint (account s)

  occupancyReading : State → ℕ
  occupancyReading s = R.polarizedReading 0ℙ (account s)

  freeReading : State → ℕ
  freeReading s = R.polarizedReading 1ℙ (capacityAccount s)

  Occupancy≡reading : ∀ s → Occupancy s ≡ occupancyReading s
  Occupancy≡reading s = ≡-sym (ℕ-∸-⊓ (head s) (tail s))

  Free≡reading : ∀ s → Free s ≡ freeReading s
  Free≡reading s = ≡-sym (ℕ-∸-⊓ (tail s ℕ.+ N) (head s))

  enqueuePosting : T
  enqueuePosting = 1 // 0

  dequeuePosting : T
  dequeuePosting = 0 // 1

  accountEmpty : account emptyState ≈ᵀ εᵀ
  accountEmpty = ≡-refl

  private
    +-oneʳ : ∀ n → n ℕ.+ 1 ≡ ℕ.suc n
    +-oneʳ n = ≡-trans (ℕ.+-suc n 0) (cong ℕ.suc (ℕ.+-identityʳ n))

  enqueuePosts : ∀ s room → account (enqueue s room) ≈ᵀ account s ∙ᵀ enqueuePosting
  enqueuePosts s _ =
    let h = head s
        t = tail s
    in ≡-trans
      (cong (λ x → ℕ.suc h ℕ.+ x) (ℕ.+-identityʳ t))
      (cong (λ x → x ℕ.+ t) (≡-sym (+-oneʳ h)))

  dequeuePosts : ∀ s item → account (dequeue s item) ≈ᵀ account s ∙ᵀ dequeuePosting
  dequeuePosts s _ =
    let h = head s
        t = tail s
    in ≡-trans
      (cong (λ x → h ℕ.+ x) (+-oneʳ t))
      (cong (λ x → x ℕ.+ ℕ.suc t) (≡-sym (ℕ.+-identityʳ h)))

  readingBalanceSheet : ∀ s → Safe s → occupancyReading s ℕ.+ freeReading s ≡ N
  readingBalanceSheet s ok = ≡-trans
    (cong₂ ℕ._+_ (≡-sym (Occupancy≡reading s)) (≡-sym (Free≡reading s)))
    rawBalance
    where
    rawBalance : Occupancy s ℕ.+ Free s ≡ N
    rawBalance =
      let h = head s
          t = tail s
          o = Occupancy s
          o≤N = ℕ.m≤n+o⇒m∸n≤o h t (noOverflow ok)
          t+o≡h = ≡-trans (ℕ.+-comm t o) (ℕ.m∸n+n≡m (noUnderflow ok))
          free≡N∸o = ≡-trans
            (cong (λ x → (t ℕ.+ N) ℕ.∸ x) (≡-sym t+o≡h))
            (ℕ.[m+n]∸[m+o]≡n∸o t N o)
      in ≡-trans
        (cong (λ x → o ℕ.+ x) free≡N∸o)
        (ℕ.m+[n∸m]≡n o≤N)

  balanceSheet : ∀ s → Safe s → Occupancy s ℕ.+ Free s ≡ N
  balanceSheet s ok = ≡-trans
    (cong₂ ℕ._+_ (Occupancy≡reading s) (Free≡reading s))
    (readingBalanceSheet s ok)

  ----------------------------------------------------------------------
  -- Verified layer: the same guard propositions drive the typed API.

  record Verified : Set where
    constructor verified
    field
      state : State
      proof : Safe state

  open Verified public

  empty : Verified
  empty = verified emptyState emptySafe

  enqueueᵛ : (b : Verified) → HasRoom (state b) → Verified
  enqueueᵛ b room = verified (enqueue (state b) room)
                             (enqueueSafe (state b) (proof b) room)

  dequeueᵛ : (b : Verified) → HasItem (state b) → Verified
  dequeueᵛ b item = verified (dequeue (state b) item)
                             (dequeueSafe (state b) (proof b) item)

------------------------------------------------------------------------
-- A worked example
--
-- Two incommensurate currencies (a 2-vector of [usd , eur]) and three
-- accounts. A $10 cash sale is recorded by debiting Cash and crediting
-- Revenue -- one swap transaction.

module ExampleSystem where

  open Accounting 2 3

  usd eur : Amount
  usd = 1 ∷ 0 ∷ []
  eur = 0 ∷ 1 ∷ []

  cash revenue equity : Fin 3
  cash    = zero
  revenue = suc zero
  equity  = suc (suc zero)

  -- Scalar multiplication of an amount (k copies of a currency).
  infixl 7 _*_
  _*_ : ℕ → Amount → Amount
  k * x = Vec.map (k ℕ.*_) x

  -- Debit Cash, credit Revenue, $10. Balanced by construction.
  cashSale : Tx
  cashSale = swap (10 * usd) cash revenue
