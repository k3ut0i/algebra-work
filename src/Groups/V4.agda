module Groups.V4 where

open import Algebra
open import Relation.Binary using (Rel; Symmetric)
open import Relation.Binary.PropositionalEquality as E using (sym; trans; cong; cong₂)
open import Agda.Builtin.Equality using(_≡_)
open import Data.Product using(_,_; _×_)

data MySet : Set where
  z : MySet
  a : MySet
  b : MySet
  c : MySet

inv : MySet → MySet
inv x = x

_≈_ : Rel MySet _
x ≈ y = (x ≡ y)

isEquivalence : Relation.Binary.IsEquivalence _≈_
isEquivalence = record { refl = _≡_.refl ;
                         sym = sym ;
                         trans = trans }

_∙_ : MySet -> MySet -> MySet
z ∙ y = y
a ∙ z = a
a ∙ a = z
a ∙ b = c
a ∙ c = b
b ∙ z = b
b ∙ a = c
b ∙ b = z
b ∙ c = a
c ∙ z = c
c ∙ a = b
c ∙ b = a
c ∙ c = z

isId : (x : MySet) → ((x ∙ z) ≈ x)
isId z = E.refl
isId a = E.refl
isId b = E.refl
isId c = E.refl

invx : (x : MySet) → (inv x ∙ x) ≈ z
invx z = E.refl
invx a = E.refl
invx b = E.refl
invx c = E.refl

∙-sym : Symmetric _≈_
∙-sym E.refl = E.refl

isInverse : Inverse _≈_ z inv _∙_
isInverse = invx , λ x → trans E.refl (invx x)

isAssoc : (x : MySet) → (y : MySet) → (w : MySet) →
             ((x ∙ y) ∙ w) ≈ (x ∙ (y ∙ w))
isAssoc z y w = E.refl
isAssoc a z w = E.refl
isAssoc a a z = E.refl
isAssoc a a a = E.refl
isAssoc a a b = E.refl
isAssoc a a c = E.refl
isAssoc a b z = E.refl
isAssoc a b a = E.refl
isAssoc a b b = E.refl
isAssoc a b c = E.refl
isAssoc a c z = E.refl
isAssoc a c a = E.refl
isAssoc a c b = E.refl
isAssoc a c c = E.refl
isAssoc b z w = E.refl
isAssoc b a z = E.refl
isAssoc b a a = E.refl
isAssoc b a b = E.refl
isAssoc b a c = E.refl
isAssoc b b z = E.refl
isAssoc b b a = E.refl
isAssoc b b b = E.refl
isAssoc b b c = E.refl
isAssoc b c z = E.refl
isAssoc b c a = E.refl
isAssoc b c b = E.refl
isAssoc b c c = E.refl
isAssoc c z w = E.refl
isAssoc c a z = E.refl
isAssoc c a a = E.refl
isAssoc c a b = E.refl
isAssoc c a c = E.refl
isAssoc c b z = E.refl
isAssoc c b a = E.refl
isAssoc c b b = E.refl
isAssoc c b c = E.refl
isAssoc c c z = E.refl
isAssoc c c a = E.refl
isAssoc c c b = E.refl
isAssoc c c c = E.refl

V₄ : Group _ _
V₄ = record {
     Carrier = MySet ;
     _≈_ = _≈_ ;
     _∙_ = _∙_ ;
     ε = z ;
     _⁻¹ = inv ;
     isGroup = record {
               isMonoid = record {
                          isSemigroup = record {
                                        isMagma = record {
                                                  isEquivalence = isEquivalence ;
                                                  ∙-cong = cong₂ _∙_ } ;
                                        assoc = isAssoc } ;
                          identity = (λ x → E.refl) ,
                                     isId } ;
               inverse = isInverse ;
               ⁻¹-cong = λ x -> x } } 
