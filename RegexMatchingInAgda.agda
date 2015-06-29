{-#  OPTIONS --no-termination-check  #-}

module RegexMatchingInAgda where

open import Relation.Binary.PropositionalEquality
open import Data.Bool
--open import Data.Char


----------------------------------------------------
-- 1. STANDARD DATATYPES AND FUNCTIONS            --
----------------------------------------------------

-- function composition
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

data Empty : Set  where

¬ : (a : Set) → Set
¬ a = a → Empty 

data Either (A B : Set) : Set where
  Inl : A → Either A B
  Inr : B → Either A B

-- Instead of "Either a (¬ a)" we want to  write "Decision a"
data Decision (A : Set) : Set where
  Yes : A → Decision A
  No  : (¬ A) → Decision A

contradiction : {A : Set} → Empty → A
contradiction ()

-- symmetry/transitivity lemma for built-in equivalence
≡-symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
≡-symm refl = refl

≡-trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl


----------------------------------------------------
-- 1. STRINGS                                     --
----------------------------------------------------

-- simple small character set
data Char : Set where
  a' : Char
  b' : Char

data List (A : Set) : Set where
  []     : List A
  _::_ : A → List A → List A

String = List Char

-- equality test for characters
_=?=_ : (c d : Char) → Decision (c ≡ d)
a' =?= a' = Yes refl
a' =?= b' = No f
  where
  f : ¬ (a' ≡ b')
  f ()
b' =?= a' = No f
  where
  f : ¬ (b' ≡ a')
  f ()
b' =?= b' = Yes refl

-- appending strings: as a function (++) and as a datatype (Append)
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Append {a : Set} : List a → List a → List a → Set where
  Base : ∀ {xs} → Append [] xs xs
  Step : ∀ {x xs ys zs} → (app : Append xs ys zs) → Append (x :: xs) ys (x :: zs)

-- proofs that these definitions are actually equivalent
appendCorrect : {a : Set} {xs ys zs : List a} → Append xs ys zs → zs ≡ xs ++ ys
appendCorrect Base = refl
appendCorrect (Step {x} p) = cong (λ s → (x :: s)) (appendCorrect p)

appendComplete : {a : Set} {xs ys : List a} → Append xs ys (xs ++ ys)
appendComplete {xs = []} = Base
appendComplete {xs = x :: xs} = Step (appendComplete {_} {xs})

-- associativity lemmas for both ++ and Append
++-ass : (xs ys zs : String)  → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
++-ass [] ys zs = refl
++-ass (x :: xs) ys zs = cong (_::_ x) (++-ass xs ys zs)

appendAss₁ : (ws xs ys zs : String) → Append (ws ++ xs) ys zs → Append ws (xs ++ ys) zs
appendAss₁ [] xs ys zs p rewrite appendCorrect p = Base
appendAss₁ (x :: ws) xs ys ._ (Step p) = Step (appendAss₁ ws xs ys _ p)

appendAss₂ : (ws xs ys zs : String) → Append ws (xs ++ ys) zs → Append (ws ++ xs) ys zs
appendAss₂ [] xs ys .(xs ++ ys) Base = appendComplete
appendAss₂ (x :: ws) xs ys ._ (Step p) = Step (appendAss₂ ws xs ys _ p)

-- Some more lemmas about append
append-[] : (s : String) → Append s [] s
append-[] [] = Base
append-[] (x :: s) = Step (append-[] s)

append-unique : {a : Set} {xs ys zs zs' : List a} → Append xs ys zs → Append xs ys zs' → zs ≡ zs'
append-unique Base Base = refl
append-unique (Step {x} app1) (Step app2) = cong (λ s → (x :: s)) (append-unique app1 app2) 

[]-right : (s : String) → (s ++ []) ≡ s
[]-right [] = refl
[]-right (x :: xs) = cong ((_::_) x) ([]-right xs)

----------------------------------------------------
-- 3. REGULAR EXPRESSIONS                         --
----------------------------------------------------

data Regex : Set where
  ε   : Regex
  ∅   : Regex
  ch  : Char -> Regex
  _∣_  : Regex → Regex → Regex
  _·_ : Regex → Regex → Regex
  _⋆  : Regex → Regex

data _∈_ : String -> Regex -> Set where
  ε-def  : []  ∈ ε
  ch-def : (c : Char) -> (c :: []) ∈ ch c
  ∣-left  : ∀ {s r₁ r₂}        → s ∈ r₁   → s ∈ (r₁ ∣ r₂)
  ∣-right : ∀ {s r₁ r₂}        → s ∈ r₂   → s ∈ (r₁ ∣ r₂)
  concat : ∀ {s₁ s₂ s₃ r₁ r₂} → s₁ ∈ r₁   → s₂ ∈ r₂      → Append s₁ s₂ s₃ → s₃ ∈ (r₁ · r₂)
  ⋆-base : ∀ {r}              → [] ∈ r ⋆
  ⋆-step : ∀ {s₁ s₂ s₃ r}     → s₁ ∈ r    → s₂ ∈ r ⋆     → Append s₁ s₂ s₃ → s₃ ∈ r ⋆


----------------------------------------------------
-- 4. EQUIVALENCE                                 --
----------------------------------------------------

data _∼_ : Regex → Regex → Set where
  ext  : {r₁ r₂ : Regex} → ({s : String} → s ∈ r₁ → s ∈ r₂) →
                           ({s : String} → s ∈ r₂ → s ∈ r₁) → r₁ ∼ r₂

fst : {r t : Regex} → r ∼ t → ({s : String} → s ∈ r → s ∈ t)
fst (ext f g) = f

snd : {r t : Regex} → r ∼ t → ({s : String} → s ∈ t → s ∈ r)
snd (ext f g) = g

-- ∼ is an equivalence relation:
∼refl : {r : Regex} → r ∼ r
∼refl = ext (λ x → x) (λ x → x)

∼symm : {r t : Regex} → r ∼ t → t ∼ r
∼symm (ext f g) = ext g f

∼trans : {r t u : Regex} → r ∼ t → t ∼ u → r ∼ u
∼trans (ext f₁ g₁) (ext f₂ g₂) = ext (f₂ ∘ f₁) (g₁ ∘ g₂)

-- Some syntactic sugar:
infixr 2 _⟨_⟩_
_⟨_⟩_ : (r : Regex) -> {t u : Regex} → r ∼ t → t ∼ u → r ∼ u
x ⟨ p ⟩ q = ∼trans p q

_■ : forall (r : Regex) -> r ∼ r
_■ r = ∼refl

-- General helper lemma's
consume-⋆ : ∀ {r s} → s ∈ (r · (r ⋆)) → s ∈ (r ⋆)
consume-⋆ (concat p p₁ app) = ⋆-step p p₁ app

--******* A. Properties of ∣ *******--
∣-comm : {r t : Regex} → (r ∣ t) ∼ (t ∣ r)
∣-comm = ext f f
  where
  f : ∀ {s r t} → s ∈ (r ∣ t) → s ∈ (t ∣ r)
  f (∣-left  p) = ∣-right p
  f (∣-right p) = ∣-left  p

∣-id-right : {r : Regex} → (r ∣ ∅) ∼ r
∣-id-right = ext f ∣-left
  where
  f : ∀ {s r} → s ∈ (r ∣ ∅) → s ∈ r
  f (∣-left p) = p
  f (∣-right ())

∣-id-left : {r : Regex} → (∅ ∣ r) ∼ r
∣-id-left {r} = (∅ ∣ r) ⟨ ∣-comm ⟩ (r ∣ ∅) ⟨ ∣-id-right ⟩ r ■ 

∣-idem : {r : Regex} → (r ∣ r) ∼ r
∣-idem = ext f g
  where
  f : ∀ {s r} → s ∈ (r ∣ r) → s ∈ r
  f (∣-left p)  = p
  f (∣-right p) = p
  g : ∀ {s r} → s ∈ r → s ∈ (r ∣ r)
  g p = ∣-left p

∣-ass : {r t u : Regex} → ((r ∣ t) ∣ u) ∼ (r ∣ (t ∣ u))
∣-ass = ext f g
  where
  f : ∀ {s r t u} → s ∈ ((r ∣ t) ∣ u) → s ∈ (r ∣ (t ∣ u))
  f (∣-left (∣-left  p)) = ∣-left p           -- case: s ∈ r
  f (∣-left (∣-right p)) = ∣-right (∣-left p) -- case: s ∈ t
  f (∣-right p)         = ∣-right (∣-right p) -- case: s ∈ u
  g : ∀ {s r t u} → s ∈ (r ∣ (t ∣ u)) → s ∈ ((r ∣ t) ∣ u)
  g (∣-left p)           = ∣-left (∣-left p)   -- case: s ∈ r
  g (∣-right (∣-left  p)) = ∣-left (∣-right p) -- case: s ∈ t
  g (∣-right (∣-right p)) = ∣-right p          -- case: s ∈ u


--******* B. Properties of · *******--
·-null-right : {r : Regex} → (r · ∅) ∼ ∅
·-null-right = ext f g
  where
  f : ∀ {s r} → s ∈ (r · ∅) → s ∈ ∅
  f (concat _ () _)
  g : ∀ {s r } → s ∈ ∅ → s ∈ (r · ∅)
  g ()

·-null-left : {r : Regex} → (∅ · r) ∼ ∅
·-null-left = ext f g
  where
  f : ∀ {s r} → s ∈ (∅ · r) → s ∈ ∅
  f (concat () _ _)
  g : ∀ {s r } → s ∈ ∅ → s ∈ (∅ · r)
  g ()

·-id-right : {r : Regex} → (r · ε) ∼ r
·-id-right = ext f g
  where
  f : ∀ {s r} → s ∈ (r · ε) → s ∈ r
  f (concat p ε-def app) rewrite append-unique app (append-[] _) = p
  g : ∀ {s r} → s ∈ r → s ∈ (r · ε)
  g p = concat p ε-def (append-[] _)

·-id-left : {r : Regex} → (ε · r) ∼ r
·-id-left = ext f g
  where
  f : ∀ {s r} → s ∈ (ε · r) → s ∈ r
  f (concat ε-def p Base) = p
  g : ∀ {s r} → s ∈ r → s ∈ (ε · r)
  g p = concat ε-def p Base

·-ass : {r t u : Regex} → ((r · t) · u) ∼ (r · (t · u))
·-ass = ext f g
  where
    f :  {s : String} → {r t u : Regex} → s ∈ ((r · t) · u) → s ∈ (r · (t · u))
    f (concat {._} {s₃} (concat {s₁} {s₂} x₁ x₂ app₁) x₃ app₂)
       rewrite appendCorrect app₁ | appendCorrect app₂ | ++-ass s₁ s₂ s₃
       = concat x₁ (concat x₂ x₃ appendComplete) appendComplete
    g :  {s : String} → {r t u : Regex} → s  ∈ (r · (t · u)) → s ∈ ((r · t) · u)
    g (concat {s₁} {._} x₁ (concat {s₂} {s₃} x₂ x₃ app₁) app₂)
       rewrite appendCorrect app₁ | appendCorrect app₂ | ≡-symm (++-ass s₁ s₂ s₃)
       = concat (concat x₁ x₂ appendComplete) x₃ appendComplete





--******* C. Distributive properties *******--
dist-left : {r t u : Regex} → (r · (t ∣ u)) ∼ ((r · t) ∣ (r · u))
dist-left = ext f g
  where
  f : ∀ {s r t u} → s ∈ (r · (t ∣ u)) → s ∈ ((r · t) ∣ (r · u))
  f (concat p₁ (∣-left p₂) app)  = ∣-left (concat p₁ p₂ app)
  f (concat p₁ (∣-right p₂) app) = ∣-right (concat p₁ p₂ app)
  g : ∀ {s r t u} → s ∈ ((r · t) ∣ (r · u)) → s ∈ (r · (t ∣ u))
  g (∣-left  (concat p₁ p₂ app)) = concat p₁ (∣-left p₂) app
  g (∣-right (concat p₁ p₂ app)) = concat p₁ (∣-right p₂) app

dist-right : {r t u : Regex} → ((t ∣ u) · r) ∼ ((t · r) ∣ (u · r))
dist-right = ext f g
  where
  f : ∀ {s r t u} → s ∈ ((t ∣ u) · r) → s ∈ ((t · r) ∣ (u · r))
  f (concat (∣-left p₁)  p₂ app) = ∣-left  (concat p₁ p₂ app)
  f (concat (∣-right p₁) p₂ app) = ∣-right (concat p₁ p₂ app)
  g : ∀ {s r t u} → s ∈ ((t · r) ∣ (u · r)) → s ∈ ((t ∣ u) · r)
  g (∣-left  (concat p₁ p₂ app)) = concat (∣-left p₁ ) p₂ app
  g (∣-right (concat p₁ p₂ app)) = concat (∣-right p₁) p₂ app



--******* D. Closure properties *******--
null-closure : (∅ ⋆) ∼ ε
null-closure = ext f g
  where
  f : ∀ {s} → s ∈ (∅ ⋆) → s ∈ ε
  f ⋆-base = ε-def
  f (⋆-step () _ _)
  g : ∀ {s} → s ∈ ε → s ∈ (∅ ⋆)
  g ε-def = ⋆-base

epsilon-closure : (ε ⋆) ∼ ε
epsilon-closure = ext f g
  where
  f : ∀ {s} → s ∈ (ε ⋆) → s ∈ ε
  f ⋆-base = ε-def
  f (⋆-step {[]}     ε-def x Base) = f x
  f (⋆-step {_ :: _} ()    _ _) 
  g : ∀ {s} → s ∈ ε → s ∈ (ε ⋆)
  g ε-def = ⋆-base

⋆-rep : {r : Regex} → ((r ⋆) · (r ⋆)) ∼ (r ⋆)
⋆-rep = ext f g
  where
  f' : ∀ {s₁ s₂ r} → s₁ ∈ (r ⋆) → s₂ ∈ (r ⋆) → (s₁ ++ s₂) ∈ (r ⋆)
  f' ⋆-base p₂ = p₂
  f' {._} {s₃} (⋆-step {s₁} {s₂} p₁ p₂ app) p₃ rewrite appendCorrect app | ++-ass s₁ s₂ s₃
       = ⋆-step p₁ (f' p₂ p₃) appendComplete
  f : ∀ {s r} → s ∈ ((r ⋆) · (r ⋆)) → s ∈ (r ⋆)
  f (concat p₁ p₂ app) rewrite appendCorrect app = f' p₁ p₂
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ ((r ⋆) · (r ⋆))
  g p = concat ⋆-base p Base

⋆-comp : {r : Regex} → ((r ⋆) ⋆) ∼ (r ⋆)
⋆-comp = ext f g
  where
  f : ∀ {s r} → s ∈ ((r ⋆) ⋆) → s ∈ (r ⋆)
  f ⋆-base = ⋆-base
  f {._} {r} (⋆-step {s₁} {s₂} p₁ p₂ app) with ⋆-rep {r}
  f {._} {r} (⋆-step           p₁ p₂ app) | ext f' g' = f' (concat p₁ (f p₂) app)
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ ((r ⋆) ⋆)
  g p = ⋆-step p ⋆-base (append-[] _)
  

∣-before-⋆ : {r : Regex} → (r ∣ (r ⋆)) ∼ (r ⋆)
∣-before-⋆ = ext f g
  where
  f : ∀ {s r} → s ∈ (r ∣ (r ⋆)) → s ∈ (r ⋆)
  f (∣-left p) = ⋆-step p ⋆-base (append-[] _)
  f (∣-right p) = p
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ (r ∣ (r ⋆))
  g p = ∣-right p

ε-idem₁ : {r : Regex} → (ε ∣ (r ⋆)) ∼ (r ⋆)
ε-idem₁ = ext f g
  where
  f : ∀ {s r} → s ∈ (ε ∣ (r ⋆)) → s ∈ (r ⋆)
  f (∣-left ε-def) = ⋆-base
  f (∣-right p) = p
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ (ε ∣ (r ⋆))
  g p = ∣-right p

ε-idem₂ : {r : Regex} → ((ε ∣ r) ⋆) ∼ (r ⋆)
ε-idem₂ = ext f g
  where
  f : ∀ {s r} → s ∈ ((ε ∣ r) ⋆) → s ∈ (r ⋆)
  f ⋆-base = ⋆-base
  f (⋆-step (∣-left ε-def) p Base) = f p
  f (⋆-step (∣-right p₁) p₂ app) = ⋆-step p₁ (f p₂) app
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ ((ε ∣ r) ⋆)
  g ⋆-base = ⋆-base
  g (⋆-step p₁ p₂ app) = ⋆-step (∣-right p₁) (g p₂) app

ε-idem₃ : {r : Regex} → ((ε ∣ r) · (r ⋆)) ∼ (r ⋆)
ε-idem₃ = ext f g
  where
  f : ∀ {s r} → s ∈ ((ε ∣ r) · (r ⋆)) → s ∈ (r ⋆)
  f (concat (∣-left ε-def) p Base) = p
  f (concat (∣-right p₁) p₂ app) = ⋆-step p₁ p₂ app
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ ((ε ∣ r) · (r ⋆))
  g p = concat (∣-left ε-def) p Base


ε-idem₄ : {r : Regex} → (ε ∣ (r · (r ⋆))) ∼ (r ⋆)
ε-idem₄ = ext f g
  where
  f : ∀ {s r} → s ∈ (ε ∣ (r · (r ⋆))) → s ∈ (r ⋆)
  f (∣-left ε-def) = ⋆-base
  f (∣-right (concat p₁ p₂ app)) = ⋆-step p₁ p₂ app
  g : ∀ {s r} → s ∈ (r ⋆) → s ∈ (ε ∣ (r · (r ⋆)))
  g ⋆-base = ∣-left ε-def
  g (⋆-step p₁ p₂ app) = ∣-right (concat p₁ p₂ app)

--******* E. Properties of ⋆ *******--

⋆-comm : {r : Regex} → (r · (r ⋆)) ∼ ((r ⋆) · r)
⋆-comm = ext f g
  where
  f-help₂ : ∀ {r r' t s} → s ∈ (r · t) → (∀ {s} → s ∈ r → s ∈ r') → s ∈ (r' · t)
  f-help₂ (concat p p₁ app) h = concat (h p) p₁ app
  f' : ∀ {r s₁ s₂} → s₁ ∈ r → s₂ ∈ (r ⋆) → (s₁ ++ s₂) ∈ ((r ⋆) · r)
  f' {_} {s₁} p₁ ⋆-base rewrite []-right s₁ = concat ⋆-base p₁ Base
  f' {r} {s₁} p₁ (⋆-step {s₂} {s₃} p₂ p₃ app) with appendCorrect app
  f' {r} {s₁} p₁ (⋆-step {s₂} {s₃} p₂ p₃ app) | refl with concat p₁ (f' p₂ p₃) appendComplete | ·-ass {r} {r ⋆} {r}
  f' p₁ (⋆-step p₂ p₃ app) | refl | q | ext fₐ gₐ = f-help₂ (gₐ q) consume-⋆
  f : ∀ {r s} → s ∈ (r · (r ⋆)) → s ∈ ((r ⋆) · r)
  f (concat p p₁ app) rewrite appendCorrect app = f' p p₁
  g' : ∀ {r s₁ s₂} → s₁ ∈ (r ⋆) → s₂ ∈ r → (s₁ ++ s₂) ∈ (r · (r ⋆))
  g' {r} {.[]} {s₂} ⋆-base p₂ = concat p₂ (⋆-base {r}) (append-[] s₂)
  g' {_} {._} {s₃} (⋆-step {s₁} {s₂} p₁ p₂ app) p₃ rewrite ++-ass s₁ s₂ s₃ | appendCorrect app
       = concat p₁ (consume-⋆ (g' p₂ p₃)) (appendAss₁ s₁ s₂ s₃ _ appendComplete)
  g : ∀ {r s} → s ∈ ((r ⋆) · r) → s ∈ (r · (r ⋆))
  g (concat p p₁ app) rewrite appendCorrect app = g' p p₁


----------------------------------------------------
-- 5. MATCHING ALGORITHM (HARPER)                 --
----------------------------------------------------

acc : (r : Regex) → (s : String) → ((s' : String) → Bool) → Bool
acc ε s k = k s
acc ∅ _ _ = false
acc (ch _) [] _ = false
acc (ch c) (d :: ds) k with c =?= d
acc (ch c) (.c :: ds) k | Yes refl = k ds
acc (ch c) (d :: ds) _  | No _     = false
acc (r₁ ∣ r₂) s k with acc r₁ s k
... | true  = true
... | false = acc r₂ s k
acc (r₁ · r₂) s k = acc r₁ s (λ s' → acc r₂ s' k)
acc (r ⋆) s k with k s
... | true  = true
... | false = acc r s (λ s' → acc (r ⋆) s' k)

accept : (r : Regex) → (s : String) → Bool
accept r s = acc r s f
  where
  f : String → Bool
  f [] = true
  f (x :: s₁) = false

----------------------------------------------------
-- 6. AUTOMATIC PROOF CONSTRUCTION (non-terminating)
----------------------------------------------------

acc' : {r' : Regex} → (r : Regex) → (s : String) →
       ((s' : String) → Decision (s' ∈ r')) →
       Decision (s ∈ (r · r'))
acc' {r'} ε s k with k s | ·-id-left {r'}
acc' ε s k | Yes p | ext f g = Yes (g p)
acc' ε s k | No  p | ext f g = No (λ q → p (f q))
acc' ∅ s k = No f
  where
  f : ∀ {s r} → ¬ (s ∈ (∅ · r))
  f (concat () _ _)
acc' (ch c) [] k = No f
  where
  f : ∀ {c r} → ¬ ([] ∈ (ch c · r))
  f (concat () _ Base)
acc' (ch c) (d :: ds)  k with c =?= d
acc' (ch c) (.c :: ds) k | Yes refl = f (k ds)
  where
  lemma : ∀ {c ds r} → (c :: ds) ∈ (ch c · r) → ds ∈ r
  lemma (concat () _  Base)
  lemma (concat _  p₂ (Step Base)) = p₂
  lemma (concat () _  (Step (Step _)))
  f : ∀ {c ds r} → Decision (ds ∈ r) → Decision ((c :: ds) ∈ (ch c · r))
  f {c} (Yes x) = Yes (concat (ch-def c) x (Step Base))
  f     (No  x) = No  (λ y → x (lemma y))
acc' (ch c) (d :: ds) k | No x = No (λ y → x (lemma y))
  where
  lemma : ∀ {c d ds r} → (d :: ds) ∈ (ch c · r) → c ≡ d
  lemma (concat () _ Base)
  lemma (concat (ch-def _) _ (Step Base)) = refl
acc' (r₁ ∣ r₂) s k with acc' r₁ s k
acc' (r₁ ∣ r₂) s k | Yes (concat p₁ p₂ app)         = Yes (concat (∣-left  p₁) p₂ app)
acc' (r₁ ∣ r₂) s k | No  x with acc' r₂ s k
acc' (r₁ ∣ r₂) s k | No  x | Yes (concat p₁ p₂ app) = Yes (concat (∣-right p₁) p₂ app)
acc' {r} (r₁ ∣ r₂) s k | No x | No y = No f
  where
  f : ¬ (s ∈ ((r₁ ∣ r₂) · r))
  f (concat (∣-left  p₁) p₂ app) = x (concat p₁ p₂ app)
  f (concat (∣-right p₁) p₂ app) = y (concat p₁ p₂ app)
acc' {r'} (r₁ · r₂) s k with acc' r₁ s (λ s' → acc' r₂ s' k) | ·-ass {r₁} {r₂} {r'}
acc' (r₁ · r₂) s k | Yes x | ext f' g' = Yes (g' x)
acc' (r₁ · r₂) s k | No  x | ext f' g' = No  (λ y → x (f' y))
acc'      (r ⋆) s k with k s
acc'      (r ⋆) s k | Yes x = Yes (concat ⋆-base x Base)
acc' {r'} (r ⋆) s k | No  x with acc' r s (λ s' → acc' (r ⋆) s' k) | ·-ass {r} {r ⋆} {r'}
acc'      (r ⋆) s k | No  x | Yes y | ext f' g' = Yes (lemma (g' y) f)
  where
  f : ∀ {s r} → s ∈ (r · (r ⋆)) → s ∈ (r ⋆)
  f (concat p₁ p₂ app) = ⋆-step p₁ p₂ app
  lemma : ∀ {s r r' t} → s ∈ (r · t) → (∀ {s'} → s' ∈ r → s' ∈ r') → s ∈ (r' · t)
  lemma (concat p₁ p₂ app) f = concat (f p₁) p₂ app
acc' {r'} (r ⋆) s k | No  x | No  y | ext f' g' = No f
  where
  f : ¬ (s ∈ ((r ⋆) · r'))
  f (concat ⋆-base p₂ app) with appendCorrect app
  f (concat ⋆-base p₂ app) | refl = x p₂
  f (concat {._} {s₃} (⋆-step {s₁} {s₂} p₁ p₂ app₁) p₃ app₂) with appendCorrect app₁
  ... | refl = y (f' (concat (concat p₁ p₂ app₁) p₃ app₂))


accept' : (r : Regex) → (s : String) → Decision (s ∈ r)
accept' r s = f (acc' r s k)
  where
  k-help : ∀ {x xs} → ¬ ((x :: xs) ∈ ε)
  k-help ()
  k : (s' : String) → Decision (s' ∈ ε)
  k [] = Yes ε-def
  k (_ :: _) = No k-help
  f : ∀ {s r} → Decision (s ∈ (r · ε)) → Decision (s ∈ r)
  f {_} {r} (Yes x) with ·-id-right {r}
  ... | ext f' g' = Yes (f' x)
  f {_} {r} (No  x) with ·-id-right {r}
  ... | ext f' g' = No (λ y → x (g' y))

----------------------------------------------------
-- 7. AUTOMATIC PROOF CONSTRUCTION (terminating)
----------------------------------------------------

hasEWP : (r : Regex) → Decision ([] ∈ r)
hasEWP ε = Yes ε-def
hasEWP ∅ = No  f
  where
  f : ¬ ([] ∈ ∅)
  f ()
hasEWP (ch x) = No f
  where
  f : ¬ ([] ∈ ch x)
  f ()
hasEWP (r₁ ∣ r₂) with hasEWP r₁
hasEWP (r₁ ∣ r₂) | Yes x = Yes (∣-left x)
hasEWP (r₁ ∣ r₂) | No  x with hasEWP r₂
hasEWP (r₁ ∣ r₂) | No  x | Yes y = Yes (∣-right y)
hasEWP (r₁ ∣ r₂) | No  x | No  y = No f
  where
  f : ¬ ([] ∈ (r₁ ∣ r₂))
  f (∣-left p) = x p
  f (∣-right p) = y p
hasEWP (r₁ · r₂) with hasEWP r₁
hasEWP (r₁ · r₂) | Yes x with hasEWP r₂
hasEWP (r₁ · r₂) | Yes x | Yes y = Yes (concat x y Base)
hasEWP (r₁ · r₂) | Yes x | No  y = No  f
  where
  f : ¬ ([] ∈ (r₁ · r₂))
  f (concat p₁ p₂ Base) = y p₂
hasEWP (r₁ · r₂) | No  x = No f
  where
  f : ¬ ([] ∈ (r₁ · r₂))
  f (concat p₁ p₂ Base) = x p₁
hasEWP (r ⋆) = Yes ⋆-base

_− : Regex → Regex
ε − = ∅
∅ − = ∅
ch x − = ch x
(r ∣ r₁) − = (r −) ∣ (r₁ −)
(r · r₁) − with hasEWP r | hasEWP r₁
(r · r₁) − | Yes x | Yes y = (r₁ −) ∣ ((r −) ∣ ((r −) · (r₁ −)))
(r · r₁) − | Yes x | No  y = (r₁ −)         ∣ ((r −) · (r₁ −))
(r · r₁) − | No  x | Yes y =          (r −) ∣ ((r −) · (r₁ −))
(r · r₁) − | No  x | No  y =                  (r −) · (r₁ −)
(r ⋆) − = (r −) · ((r −) ⋆)

data SF : Regex → Regex → Set where
  withEWP : ∀ {r} → ([] ∈ r) → SF r (ε ∣ (r −))
  withoutEWP : ∀ {r} → (¬ ([] ∈ r)) → SF r (r −)

lemma− : ∀ {r c s} → (c :: s) ∈ r → (c :: s) ∈ (r −)

lemma−⋆₂ : ∀ {r c s} → (c :: s) ∈ (r ⋆) → (c :: s) ∈ ((r −) ⋆)
lemma−⋆₂ (⋆-step {[]}              _  p₂ Base) = lemma−⋆₂ p₂
lemma−⋆₂ (⋆-step {_ :: _} {[]}     p₁ _  app)  = ⋆-step (lemma− p₁) ⋆-base        app 
lemma−⋆₂ (⋆-step {_ :: _} {_ :: _} p₁ p₂ app)  = ⋆-step (lemma− p₁) (lemma−⋆₂ p₂) app

lemma− (ch-def c) = ch-def c
lemma− (∣-left p)  = ∣-left  (lemma− p)
lemma− (∣-right p) = ∣-right (lemma− p)
lemma− (concat {s₁} {_} {._} {r₁} {r₂} p p₁ x) with hasEWP r₁ | hasEWP r₂
lemma− (concat {[]}              _  p₂ Base) | Yes _ | Yes _ = ∣-left (lemma− p₂)
lemma− (concat {_ :: _} {[]}     p₁ _  app)  | Yes _ | Yes _ rewrite append-unique app (append-[] _)
                                                             = ∣-right (∣-left (lemma− p₁))
lemma− (concat {_ :: _} {_ :: _} p₁ p₂ app)  | Yes _ | Yes _ = ∣-right (∣-right (concat (lemma− p₁) (lemma− p₂) app))
lemma− (concat {[]}              _  p₂ Base) | Yes _ | No  _ = ∣-left (lemma− p₂)
lemma− (concat {_ :: _} {[]}     _  p₂ app)  | Yes _ | No  y = contradiction (y p₂)
lemma− (concat {_ :: _} {_ :: _} p₁ p₂ app)  | Yes _ | No  _ = ∣-right (concat (lemma− p₁) (lemma− p₂) app)
lemma− (concat {[]}              p₁ p₂ Base) | No  x | Yes _ = contradiction (x p₁)
lemma− (concat {_ :: _} {[]}     p₁ p₂ app)  | No  _ | Yes _ rewrite append-unique app (append-[] _)
                                                             = ∣-left (lemma− p₁)
lemma− (concat {_ :: _} {_ :: _} p₁ p₂ app)  | No  _ | Yes _ = ∣-right (concat (lemma− p₁) (lemma− p₂) app)
lemma− (concat {[]}              p₁ _  app)  | No  x | No  _ = contradiction (x p₁)
lemma− (concat {_ :: _} {[]}     _  p₂ app)  | No  _ | No  y = contradiction (y p₂)
lemma− (concat {_ :: _} {_ :: _} p₁ p₂ app)  | No  _ | No  _ = concat (lemma− p₁) (lemma− p₂) app
lemma− (⋆-step {[]}              _  p₂ Base) = lemma−  p₂
lemma− (⋆-step {_ :: _} {[]}     p₁ _  app) rewrite append-unique app (append-[] _)
                                            = concat (lemma− p₁) ⋆-base (append-[] _)
lemma− (⋆-step {_ :: _} {_ :: _} p₁ p₂ app) = concat (lemma− p₁) (lemma−⋆₂ p₂) app

lemma−₂ : ∀ {r s} → s ∈ (r −) → s ∈ r

lemma−⋆ : ∀ {r s} → s ∈ ((r −) ⋆) → s ∈ (r ⋆)
lemma−⋆ ⋆-base = ⋆-base
lemma−⋆ (⋆-step p₁ p₂ app) = ⋆-step (lemma−₂ p₁) (lemma−⋆ p₂) app

lemma−₂ {ε} ()
lemma−₂ {∅} ()
lemma−₂ {ch x} p = p
lemma−₂ {r₁ ∣ r₂} (∣-left p)  = ∣-left  (lemma−₂ p)
lemma−₂ {r₁ ∣ r₂} (∣-right p) = ∣-right (lemma−₂ p)
lemma−₂ {r₁ · r₂} p with hasEWP r₁ | hasEWP r₂
lemma−₂ {r₁ · r₂} (∣-left p)                            | Yes x | Yes y = concat x (lemma−₂ p) Base
lemma−₂ {r₁ · r₂} (∣-right (∣-left p))                   | Yes x | Yes y = concat (lemma−₂ p) y (append-[] _)
lemma−₂ {r₁ · r₂} (∣-right (∣-right (concat p₁ p₂ app))) | Yes x | Yes y = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemma−₂ {r₁ · r₂} (∣-left p)                   | Yes x | No  y = concat x (lemma−₂ p) Base
lemma−₂ {r₁ · r₂} (∣-right (concat p₁ p₂ app)) | Yes x | No  y = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemma−₂ {r₁ · r₂} (∣-left p)                   | No  x | Yes y = concat (lemma−₂ p) y (append-[] _)
lemma−₂ {r₁ · r₂} (∣-right (concat p₁ p₂ app)) | No  x | Yes y = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemma−₂ {r₁ · r₂} (concat p₁ p₂ app)           | No  x | No  y = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemma−₂ {r ⋆} (concat p₁ p₂ app) = ⋆-step (lemma−₂ p₁) (lemma−⋆ p₂) app

lemmaDerivEquiv : ∀ {r'} (r : Regex) → SF r r' → r ∼ r'
lemmaDerivEquiv ε        (withEWP _)    = ∼symm ∣-id-right
lemmaDerivEquiv ε        (withoutEWP x) = contradiction (x ε-def)
lemmaDerivEquiv ∅        (withEWP ())
lemmaDerivEquiv ∅        (withoutEWP x) = ∼refl
lemmaDerivEquiv (ch c)   (withEWP ())
lemmaDerivEquiv (ch c)   (withoutEWP x) = ∼refl
lemmaDerivEquiv (r₁ ∣ r₂) (withEWP x)   = ext f g
  where
  f : ∀ {s} → s ∈ (r₁ ∣ r₂) → s ∈ (ε ∣ ((r₁ −) ∣ (r₂ −)))
  f {[]}     p           = ∣-left ε-def
  f {_ :: _} (∣-left p)  = ∣-right (∣-left  (lemma− p))
  f {_ :: _} (∣-right p) = ∣-right (∣-right (lemma− p))
  g : ∀ {s} → s ∈ (ε ∣ ((r₁ −) ∣ (r₂ −))) → s ∈ (r₁ ∣ r₂)
  g {[]}     _                    = x
  g {_ :: _} (∣-left ())
  g {_ :: _} (∣-right (∣-left p))  = ∣-left  (lemma−₂ p)
  g {_ :: _} (∣-right (∣-right p)) = ∣-right (lemma−₂ p)
lemmaDerivEquiv (r₁ ∣ r₂) (withoutEWP x) = ext f g
  where
  f : ∀ {s} → s ∈ (r₁ ∣ r₂) → s ∈ ((r₁ −) ∣ (r₂ −))
  f {[]} (∣-left p)      = contradiction (x (∣-left  p))
  f {[]} (∣-right p)     = contradiction (x (∣-right p))
  f {_ :: _} (∣-left p)  = ∣-left  (lemma− p)
  f {_ :: _} (∣-right p) = ∣-right (lemma− p)
  g : ∀ {s} → s ∈ ((r₁ −) ∣ (r₂ −)) → s ∈ (r₁ ∣ r₂)
  g (∣-left p)  = ∣-left  (lemma−₂ p)
  g (∣-right p) = ∣-right (lemma−₂ p)
lemmaDerivEquiv (r₁ · r₂) (withEWP x) with hasEWP r₁ | hasEWP r₂
lemmaDerivEquiv (r₁ · r₂) (withEWP x) | Yes y₁ | Yes y₂ = ext f g
  where
  f : ∀ {s} → s ∈ (r₁ · r₂) → s ∈ (ε ∣ ((r₂ −) ∣ ((r₁ −) ∣ ((r₁ −) · (r₂ −)))))
  f {[]} p = ∣-left ε-def
  f {_ :: _} (concat {[]}              p₁ p₂ Base) = ∣-right (∣-left (lemma− p₂))
  f {_ :: _} (concat {_ :: _} {[]}     p₁ p₂ app)
           rewrite append-unique app (append-[] _) = ∣-right (∣-right (∣-left (lemma− p₁)))
  f {_ :: _} (concat {_ :: _} {_ :: _} p₁ p₂ app)  = ∣-right (∣-right (∣-right (concat (lemma− p₁) (lemma− p₂) app)))
  g : ∀ {s} → s ∈ (ε ∣ ((r₂ −) ∣ ((r₁ −) ∣ ((r₁ −) · (r₂ −))))) → s ∈ (r₁ · r₂)
  g (∣-left ε-def) = x
  g (∣-right (∣-left p))                            = concat y₁ (lemma−₂ p) Base
  g (∣-right (∣-right (∣-left p)))                   = concat (lemma−₂ p) y₂ (append-[] _)
  g (∣-right (∣-right (∣-right (concat p₁ p₂ app)))) = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemmaDerivEquiv (r₁ · r₂) (withEWP (concat p₁ p₂ Base)) | Yes y₁ | No y₂ = contradiction (y₂ p₂)
lemmaDerivEquiv (r₁ · r₂) (withEWP (concat p₁ p₂ Base)) | No  y₁ | _    = contradiction (y₁ p₁)
lemmaDerivEquiv (r₁ · r₂) (withoutEWP x) with hasEWP r₁ | hasEWP r₂
lemmaDerivEquiv (r₁ · r₂) (withoutEWP x) | Yes y₁ | Yes y₂ = contradiction (x (concat y₁ y₂ Base))
lemmaDerivEquiv (r₁ · r₂) (withoutEWP x) | Yes y₁ | No  y₂ = ext f g
  where
  f : ∀ {s} → s ∈ (r₁ · r₂) → s ∈ ((r₂ −) ∣ ((r₁ −) · (r₂ −)))
  f {[]} p = contradiction (x p)
  f {_ :: _} (concat {_}      {[]}     p₁ p₂ app) = contradiction (y₂ p₂)
  f {_ :: _} (concat {[]}     {_ :: _} p₁ p₂ app)
                   rewrite append-unique app Base = ∣-left (lemma− p₂)
  f {_ :: _} (concat {_ :: _} {_ :: _} p₁ p₂ app) = ∣-right (concat (lemma− p₁) (lemma− p₂) app)
  g : ∀ {s} → s ∈ ((r₂ −) ∣ ((r₁ −) · (r₂ −))) → s ∈ (r₁ · r₂)
  g (∣-left p)                   = concat y₁           (lemma−₂ p) Base
  g (∣-right (concat p₁ p₂ app)) = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemmaDerivEquiv (r₁ · r₂) (withoutEWP x) | No  y₁ | Yes y₂ = ext f g
  where
  f : ∀ {s} → s ∈ (r₁ · r₂) → s ∈ ((r₁ −) ∣ ((r₁ −) · (r₂ −)))
  f (concat {[]}              p₁ p₂ Base)  = contradiction (y₁ p₁)
  f (concat {_ :: _} {[]}     p₁ p₂ app)
   rewrite append-unique app (append-[] _) = ∣-left (lemma− p₁)
  f (concat {_ :: _} {_ :: _} p₁ p₂ app)   = ∣-right (concat (lemma− p₁) (lemma− p₂) app)
  g : ∀ {s} → s ∈ ((r₁ −) ∣ ((r₁ −) · (r₂ −))) → s ∈ (r₁ · r₂)
  g (∣-left   p)                 = concat (lemma−₂ p)   y₂          (append-[] _)
  g (∣-right (concat p₁ p₂ app)) = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemmaDerivEquiv (r₁ · r₂) (withoutEWP x) | No  y₁ | No  y₂ = ext f g
  where
  f : ∀ {s} → s ∈ (r₁ · r₂) → s ∈ ((r₁ −) · (r₂ −))
  f (concat {[]}              p₁ p₂ app) = contradiction (y₁ p₁)
  f (concat {_ :: _} {[]}     p₁ p₂ app) = contradiction (y₂ p₂)
  f (concat {_ :: _} {_ :: _} p₁ p₂ app) = concat (lemma− p₁) (lemma− p₂) app
  g : ∀ {s} → s ∈ ((r₁ −) · (r₂ −)) → s ∈ (r₁ · r₂)
  g (concat p₁ p₂ app) = concat (lemma−₂ p₁) (lemma−₂ p₂) app
lemmaDerivEquiv (r ⋆) (withEWP x) with hasEWP r
lemmaDerivEquiv (r ⋆) (withEWP x) | Yes y with lemmaDerivEquiv r (withEWP y)
lemmaDerivEquiv (r ⋆) (withEWP x) | Yes y | ext f' g' = ext f g
  where
  f : ∀ {s} → s ∈ (r ⋆) → s ∈ (ε ∣ ((r −) · ((r −) ⋆)))
  f {[]} p = ∣-left ε-def
  f {_ :: _} (⋆-step {[]} p₁ p₂ Base) = f p₂
  f {_ :: _} (⋆-step {_ :: _} p₁ p₂ app) with f p₂
  f {_ :: _} (⋆-step {_ :: _} p₁ p₂ app) | ∣-left ε-def                = ∣-right (concat (lemma− p₁) ⋆-base app)
  f {_ :: _} (⋆-step {_ :: _} p₁ p₂ app) | ∣-right (concat q₁ q₂ app₁) = ∣-right (concat (lemma− p₁) (⋆-step q₁ q₂ app₁) app)
  g : ∀ {s} → s ∈ (ε ∣ ((r −) · ((r −) ⋆))) → s ∈ (r ⋆)
  g (∣-left   ε-def)             = ⋆-base
  g (∣-right (concat p₁ p₂ app)) = ⋆-step (lemma−₂ p₁) (lemma−⋆ p₂) app
lemmaDerivEquiv (r ⋆) (withEWP x) | No  y = ext f g
  where
  f : ∀ {s} → s ∈ (r ⋆) → s ∈ (ε ∣ ((r −) · ((r −) ⋆)))
  f ⋆-base = ∣-left ε-def
  f {[]}     (⋆-step          _  _  _)    = ∣-left ε-def
  f {_ :: _} (⋆-step {[]}     p₁ p₂ Base) = f p₂
  f {_ :: _} (⋆-step {_ :: _} p₁ p₂ app)  with f p₂
  f {_ :: _} (⋆-step {_ :: _} p₁ p₂ app) | ∣-left ε-def = ∣-right (concat (lemma− p₁) ⋆-base app)
  f {_ :: _} (⋆-step {_ :: _} p₁ p₂ app) | ∣-right (concat q₁ q₂ app₁) = ∣-right (concat (lemma− p₁) (⋆-step q₁ q₂ app₁) app)
  g : ∀ {s} → s ∈ (ε ∣ ((r −) · ((r −) ⋆))) → s ∈ (r ⋆)
  g (∣-left ε-def) = ⋆-base
  g (∣-right (concat p₁ p₂ app)) = ⋆-step (lemma−₂ p₁) (lemma−⋆ p₂) app
lemmaDerivEquiv (r ⋆) (withoutEWP x) = contradiction (x ⋆-base)

accept'' : (r : Regex) → (s : String) → Decision (s ∈ r)
accept'' r s with hasEWP r
accept'' r s | Yes x with accept' (ε ∣ (r −)) s | lemmaDerivEquiv r (withEWP x)
accept'' r s | Yes x | Yes y | ext f g = Yes (g y)
accept'' r s | Yes x | No y  | ext f g = No (λ p → y (f p))
accept'' r s | No  x with accept' (r −) s | lemmaDerivEquiv r (withoutEWP x)
accept'' r s | No  x | Yes y | ext f g = Yes (g y)
accept'' r s | No  x | No y  | ext f g = No (λ p → y (f p))


----------------------------------------------------
-- Examples
----------------------------------------------------
{-
example : Regex
example = a ∣ (b · (b · b))

example : (a' :: (b' :: (b' :: []))) ∈  (ch a' ∣ ((ch a' · ch b') · (ch  a' ∣ ch b' )))
example = ∣-right (concat (concat (ch-def a') (ch-def b') (Step Base)) (∣-right (ch-def b') ) (Step (Step Base)))

example2 : ('a' :: ('b' :: ('b' :: []))) ∈ (a ∣ ((a · b) · ( a ∣ b )  ))
example2 = ∣-right (concat (concat a-def b-def) (∣-right b-def))

example3 : "abb" ∈ (a · (b ⋆))
example3 = concat a-def (⋆-step b-def (⋆-step b-def ⋆-base))

example4 : "ab" ∈ ((a ∣ b) ⋆)
example4 = ⋆-step (∣-left a-def) (⋆-step (∣-right b-def) ⋆-base)
-}

-- PROBLEMATIC DON'T EVALUATE!!! ex = accept' ((ε ∣ ch a') ⋆) (a' :: [])
-- Ok:
--ex = accept' ((ch a' ∣ ε) ⋆) (a' :: [])








