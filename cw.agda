{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Structure using (typ) public
--open import Cubical.Foundations.GroupoidLaws renaming ( rUnit to rUnitInv ; lUnit to lUnitInv)

data RP² : Type₀ where
  0-cell : RP²
  1-cell : 0-cell ≡ 0-cell
  2-cell : Path (0-cell ≡ 0-cell) ( 1-cell ∙ 1-cell) refl 

data ℕ : Type₀ where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

Pointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Pointed ℓ = TypeWithStr ℓ (λ x → x)

pt : ∀ {ℓ} (A∙ : Pointed ℓ) → typ A∙
pt = str

Pointed₀ = Pointed ℓ-zero

{- Pointed functions -}
_→∙_ : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
_→∙_ A B = Σ[ f ∈ (typ A → typ B) ] f (pt A) ≡ pt B


{- loop space of a pointed type -}
Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)

{- n-fold loop space of a pointed type -}
Ω^_ : ∀ {ℓ} → ℕ → Pointed ℓ → Pointed ℓ
(Ω^ 0) p = p
(Ω^ (suc n)) p = Ω ((Ω^ n) p)

--_⋆_ : {A : Type₀} {base : A} → {n : ℕ} →
--      (typ ((Ω^ (suc n)) (A , base)) ) → (typ ((Ω^ (suc n)) (A , base)) ) → (typ ((Ω^ (suc n)) (A , base)) )
--α ⋆ β = α ∙ β

--comm : {A : Type₀} {base : A} →
--     (α : Path (base ≡ base) refl refl ) → ( β : Path (base ≡ base) refl refl ) → (α ∙ β) ≡ (β ∙ α)
--comm α β i j = 


data §¹ : Type₀ where
  0-cell : §¹
  1-cell : 0-cell ≡ 0-cell
  
data §² : Type₀ where
  0-cell : §²
  2-cell : Path (0-cell ≡ 0-cell) refl refl

rot§² : §² → §²
rot§² 0-cell = 0-cell
rot§² (2-cell i j) = 2-cell j i 

data §³ : Type₀ where
  0-cell : §³
  3-cell : Path (Path (0-cell ≡ 0-cell) refl refl) refl refl

data §⁴ : Type₀ where
  0-cell : §⁴
  4-cell : typ ((Ω^ 4) ( §⁴ , 0-cell ))

dim : ℕ
dim = 7

data § (n : ℕ) : Type₀ where
  0-cell : § n
  _-cell : typ ((Ω^  dim) ( § n , 0-cell ))


------------------------------------------------------
------Definitions of a variety of sphere by suspension

data Sus (A : Type₀) : Type₀ where
  north : Sus A
  south : Sus A
  merid : (a : A) → north ≡ south

data Bool : Type₀ where
  pos : Bool
  neg : Bool

_-primSphere : ℕ → Type₀
(0) -primSphere = Bool
(suc n) -primSphere = Sus ((n) -primSphere)

_+1-sphere : ℕ → Type₀
(0) +1-sphere = §¹
(suc n) +1-sphere = Sus ((n) +1-sphere)

_-sphere : ℕ → Type₀
(0) -sphere = Bool
(suc n) -sphere = (n) +1-sphere

-----------------------------------------------------


-----------------------------------------------------
--A proof of the communitativity of higher homotopy groups



data §²⋁§² : Type₀ where
  0-cell : §²⋁§²
  2-cell-1 : Path (0-cell ≡ 0-cell) refl refl
  2-cell-2 : Path (0-cell ≡ 0-cell) refl refl

--This approach turns out to be bugful
§²→§²⋁§²-1 : §² → §²⋁§²
§²→§²⋁§²-1 0-cell = 0-cell
§²→§²⋁§²-1 (2-cell i j) = (2-cell-1 ∙ 2-cell-2) i j

§²→§²⋁§²-2 : §² → §²⋁§²
§²→§²⋁§²-2 0-cell = 0-cell
§²→§²⋁§²-2 (2-cell i j) = (2-cell-2 ∙ 2-cell-1) i j

rUnit : {A : Type₀} {a , b : A} (p : Path A a b) →
                                 Path (Path A a b) (p ∙ refl) p
rUnit p k j = hcomp (λ i → λ { (j = i0) → p i0 ;
                                (j = i1) → p (i1 ) ;
                                (k = i1) → p ( j) })
                    (p (j ))

rUnitInv : {A : Type₀} {a , b : A} (p : Path A a b) →
                                 Path (Path A a b) p (p ∙ refl)
rUnitInv {A = A} {a = a} {b = b} p k j = rUnit {A} {a} {b} p (~ k) j



lUnit : {A : Type₀} {a , b : A} (p : Path A a b) →
                                 Path (Path A a b) (refl ∙ p) p
lUnit p k j = hcomp (λ i → λ { (j = i0) → p i0 ;
                                (j = i1) → p i ;
                                (k = i1) → p (i ∧ j) })
                    (p i0)

lUnitInv : {A : Type₀} {a , b : A} (p : Path A a b) →
                                 Path (Path A a b) p (refl ∙ p)
lUnitInv {A = A} {a = a} {b = b} p k j = lUnit {A} {a} {b} p (~ k) j

§²→§²⋁§²-a : §² → §²⋁§²
§²→§²⋁§²-a 0-cell = 0-cell
§²→§²⋁§²-a (2-cell i j) = ((λ k → rUnit {§²⋁§²} {0-cell} {0-cell} refl (~ k)) ∙
                           (λ k → (2-cell-1 k) ∙ refl) ∙
                           (λ k → refl ∙ (2-cell-2 k)) ∙
                           (λ k → rUnit {§²⋁§²} {0-cell} {0-cell} refl k)) i j

§²→§²⋁§²-b : §² → §²⋁§²
§²→§²⋁§²-b 0-cell = 0-cell
§²→§²⋁§²-b (2-cell i j) = ((λ k → rUnit {§²⋁§²} {0-cell} {0-cell} refl (~ k)) ∙
                           (λ k → (2-cell-1 k) ∙ (2-cell-2 k)) ∙
                           (λ k → rUnit {§²⋁§²} {0-cell} {0-cell} refl k)) i j

§²→§²⋁§²-c : §² → §²⋁§²
§²→§²⋁§²-c 0-cell = 0-cell
§²→§²⋁§²-c (2-cell i j) = ((λ k → rUnit {§²⋁§²} {0-cell} {0-cell} refl (~ k)) ∙
                           (λ k → refl ∙ (2-cell-2 k)) ∙
                           (λ k → (2-cell-1 k) ∙ refl) ∙
                           (λ k → rUnit {§²⋁§²} {0-cell} {0-cell} refl k)) i j


toCorner-1 : PathP ( λ i → (Path (0-cell ≡ 0-cell) (2-cell-1 i) (2-cell-1 i ∙ refl) )) (rUnitInv  {§²⋁§²} {0-cell} {0-cell} refl) (rUnitInv {§²⋁§²} {0-cell} {0-cell} refl)
toCorner-1 = λ i → rUnitInv {§²⋁§²} {0-cell} {0-cell} (2-cell-1 i)

toCorner-2 : PathP ( λ i → (Path (0-cell ≡ 0-cell) (2-cell-2 i) (refl ∙ 2-cell-2 i) )) (lUnitInv {§²⋁§²} {0-cell} {0-cell} refl) (lUnitInv {§²⋁§²} {0-cell} {0-cell} refl)
toCorner-2 = λ i → lUnitInv {§²⋁§²} {0-cell} {0-cell} (2-cell-2 i)

--test : Path ( Path §²⋁§² 0-cell 0-cell) refl refl
--test i j = hcomp (λ h → λ {( i = i0) → 2-cell-1 (~ h) j ;
--                             (i = i1) → 0-cell ;
--                             (j = i0) → 0-cell ;
--                             (j = i1) → 0-cell })
--                            (2-cell-2 i j)

--eq : ∀ j → 2-cell-1 i0 j ≡ 0-cell
--eq j = refl

--test-1 : ∀ i j → (test i j) ≡ (2-cell-1 ∙ 2-cell-2) i j
--test-1 i j = refl
                             

--homoComm₁ : (z : §²) → (§²→§²⋁§²-1 z ≡ §²→§²⋁§²-a z)
--homoComm₁ 0-cell = refl
--homoComm₁ (2-cell i j) k = hcomp (λ h → λ {(k = i0) →
--                                            (2-cell-1 ∙ 2-cell-2) i j ;
--                                            (i  = i0) →
--                                            rUnit {§²⋁§²} {0-cell} {0-cell} refl (h ∨ ~ k) j ;
--                                            (i  = i1) →
--                                            rUnitInv {§²⋁§²} {0-cell} {0-cell} refl k j ;
--                                            (j = i0) → 0-cell ;
--                                            (j = i1) → 0-cell })
--                                        (hcomp (λ h → λ {(i  = i1) →
--                                    (rUnitInv {§²⋁§²} {0-cell} {0-cell} refl) k j ;
--                                   (i  = i0) →
--                                    rUnitInv {§²⋁§²} {0-cell} {0-cell} (2-cell-1 (~ h)) k j ;
--                                   (j = i0) → 0-cell ;
--                                   (j = i1) → 0-cell })
--                                   (lUnitInv {§²⋁§²} {0-cell} {0-cell} (2-cell-2 i) k j))

--stretchTo-1 : §²⋁§² → §²⋁§²
--stretchTo-1 0-cell = 0-cell
--stretchTo-1 (2-cell-1 i j) = (2-cell-1 ∙ 2-cell-2 ) i j
--stretchTo-1 (2-cell-2 i j) = 0-cell

--stretch-1 : (x : §²⋁§²) → stretchTo-1 x ≡ x
--stretch-1 0-cell i = 0-cell



2-sphere-exc : 2 -primSphere  → 2 -primSphere
2-sphere-exc north = north
2-sphere-exc south = south
2-sphere-exc (merid north i) = (merid south i)
2-sphere-exc (merid south i) = (merid north i)
2-sphere-exc (merid (merid neg i) j) = (merid (merid pos (~ i)) j)
2-sphere-exc (merid (merid pos i) j) = (merid (merid neg (~ i)) j)

2-sphere-stretchTo : 2 -primSphere  → 2 -primSphere
2-sphere-stretchTo north = north
2-sphere-stretchTo south = south
2-sphere-stretchTo (merid north i) = (merid north i)
2-sphere-stretchTo (merid south i) = (merid north i)
2-sphere-stretchTo (merid (merid neg i) j) = (merid (((merid neg) ∙ (sym (merid pos))) i) j)
2-sphere-stretchTo (merid (merid pos i) j) = (merid north j)

2-sphere-stretch-1 : (x : 2 -primSphere) → ( x ≡ 2-sphere-stretchTo x)
2-sphere-stretch-1 north = refl
2-sphere-stretch-1 south = refl
2-sphere-stretch-1 (merid north i) = refl
2-sphere-stretch-1 (merid south i) j = (merid (sym (merid pos) j) i)
2-sphere-stretch-1 (merid (merid neg i) j) k = merid (hcomp (λ h → λ {(i = i0) → north ;
                                                                      (i = i1) → sym (merid pos) (k ∧ h) ;
                                                                      (k = i0) → merid neg i })
                                                             ( merid neg i))
                                                       j
2-sphere-stretch-1 (merid (merid pos i) j) k = merid (sym (merid pos) ((~ i) ∨ k)) j                                                        
                                                                      
2-sphere-stretch-2 : (x : 2 -primSphere) → (2-sphere-stretchTo x ≡ 2-sphere-exc x)
2-sphere-stretch-2 north = refl
2-sphere-stretch-2 south = refl
2-sphere-stretch-2 (merid north i) j = merid (merid neg j) i
2-sphere-stretch-2 (merid south i) = refl
2-sphere-stretch-2 (merid (merid neg i) j) k = merid (hcomp (λ h → λ {(i = i0) → merid neg k ;
                                                                      (i = i1) → merid pos (~ h) ;
                                                                      (k = i1) → sym (merid pos) (i ∧ h) })
                                                             ( merid neg (i ∨ k) ))
                                                       j
2-sphere-stretch-2 (merid (merid pos i) j) k = merid (merid neg ((~ i) ∧ k)) j                                                         

2-sphere-πrot : (x : 2 -primSphere) → (x ≡ 2-sphere-exc x)
2-sphere-πrot north = refl
2-sphere-πrot south = refl
2-sphere-πrot (merid north i) s = merid ((refl ∙ (λ j → (merid neg j))) s) i
2-sphere-πrot (merid south i) s = merid (((λ j → (sym (merid pos) j)) ∙ refl) s) i
2-sphere-πrot (merid (merid neg i) j) s = merid (((λ k → (hcomp (λ h → λ {(i = i0) → north ;
                                                                      (i = i1) → sym (merid pos) (k ∧ h) ;
                                                                      (k = i0) → merid neg i })
                                                             ( merid neg i))) ∙
                                                   (λ k → (hcomp (λ h → λ {(i = i0) → merid neg k ;
                                                                      (i = i1) → merid pos (~ h) ;
                                                                      (k = i1) → sym (merid pos) (i ∧ h) })
                                                             ( merid neg (i ∨ k) )))) s)          
                                                       j
2-sphere-πrot (merid (merid pos i) j) s = merid (((λ k → (sym (merid pos) ((~ i) ∨ k))) ∙ (λ k → (merid neg ((~ i) ∧ k)))) s ) j                                                        
--2-sphere-πrot x = (2-sphere-stretch-1 x) ∙ (2-sphere-stretch-2 x) --This would end up to a composition problem.

--homoFun→homoPath : {A : Type₀} {base : A} → (α , β : a ≡ b)

--2-Comm : {A : Type₀} {base : A} →
--      (α : typ ((Ω^ 2) (A , base)) ) → (β : typ ((Ω^ 2) (A , base)) ) → (α ∙ β ≡ β ∙ α )                                            
--2-Comm {A = A} {base = base} α β k  =  (λ i → (λ j → (f (2-sphere-πrot (merid (merid neg i) j) k)) )) ∙ (λ i → (λ j → (f (2-sphere-πrot (merid ( sym (merid pos) i) j) k)) ))
--  where
--  f : 2 -primSphere → A
--  f north = base
--  f south = base
--  f (merid north i) = base
--  f (merid south i) = base
--  f (merid (merid neg i) j) = α i j
--  f (merid (merid pos i) j) = β (~ i) j

--2-Comm : {A : Type₀} {base : A} →
--      (α : typ ((Ω^ 2) (A , base)) ) → (β : typ ((Ω^ 2) (A , base)) ) → (α ∙ β ≡ β ∙ α )    
--2-Comm {base = base} α β k i = hcomp (λ h → λ {(i = i0) → α k ;
--                                                  (i = i1) → hcomp (λ s → λ {(h = i0) → β k ;
--                                                                               (h = i1) → α (k ∧ s) ;
--                                                                               (k = i0) → β h ;
--                                                                               (k = i1) → α (s ∧ h) })
--                                                                    ( β ( k ∨ h))  })
--                                        ( hcomp (λ j → λ {(i = i0) → α k ;
--                                                            (i = i1) → β (k ∧ j) ;
--                                                            (k = i0) → α i ;
--                                                            (k = i1) → β (i ∧ j)  })
--                                                 ( α ( k ∨ i)) )

[_,_] : ∀{ℓ ℓ'} → (A : Pointed ℓ) (B : Pointed ℓ') → Type (ℓ-max ℓ ℓ')
[ A , B ] = A →∙ B

_-isContr : (A : Pointed₀) → Type₀
A -isContr = ((x : (typ A)) → ((pt A) ≡ x))

data Smash (A B : Pointed₀) : Type₀ where
  basel : Smash A B
  baser : Smash A B
  _⋀_  : (x : typ A) → (y : typ B) → Smash A B
  gluel : (a : typ A) → a ⋀ (pt B) ≡ basel
  gluer : (b : typ B) → (pt A) ⋀ b ≡ baser

SmashPt : (A B : Pointed₀) → Pointed₀
SmashPt A B = (Smash A B , basel)

basedCircle : Pointed₀
basedCircle = (§¹ , 0-cell)

--sus→loop : {A , B : Pointed₀} → ((SmashPt A basedCircle) →∙ B) → (A →∙ Ω B)
--sus→loop {A = A} {B = B} f = ( (λ (a : typ A) → ( sym ((cong (fst f)  (gluel a)) ∙ (snd f)) ) ∙∙ (λ i → ( (fst f) ( a ⋀ (1-cell i)))) ∙∙ ((cong (fst f)  (gluel a)) ∙ (snd f)) ) ,
--                       (( λ j → ( λ i → hcomp (λ k → λ {(i = i0) → hfill (λ h → λ { (k = i1) → (pt B)
--                                                                                      ; (k = i0) → (cong (fst f) (gluer (0-cell)) h) })
--                                                                                      (inS ( (sym ((cong (fst f)  (gluel (pt A))) ∙ (snd f))) (~ k) )) j ;
--                                                          (i = i1) → hfill (λ h → λ { (k = i1) → (pt B)
--                                                                                      ; (k = i0) → (cong (fst f) (gluer (0-cell)) h) })
--                                                                                      (inS (  ((cong (fst f)  (gluel (pt A))) ∙ (snd f)) k )) j })
--                                                          (cong (fst f) (gluer (1-cell i)) j)))
--                      ∙ ( λ j → ( λ i → hcomp (λ k → λ {(i = i0) →  (λ s → (hcomp (λ h → λ { (s = i1) → (pt B)
--                                                                                      ; ( s = i0) → (cong (fst f) (gluer (0-cell)) h) })
--                                                                                      ( ((cong (fst f)  (gluel (pt A))) ∙ (snd f)) s) )) (k ∧ (~ j)) ;
--                                                           (i = i1) →  (λ s → (hcomp (λ h → λ { (s = i1) → (pt B)
--                                                                                      ; ( s = i0) → (cong (fst f) (gluer (0-cell)) h) })
--                                                                                      ( ((cong (fst f)  (gluel (pt A))) ∙ (snd f)) s) )) (k ∧ (~ j)) ;
--                                                           (j = i1) → (fst f) baser }) 
--                                                           ((fst f) baser) ))) )


data ⋁₂susp (A : Type₀) : Type₀ where
  north : ⋁₂susp A
  south : ⋁₂susp A
  middle : ⋁₂susp A
  nmerid : (a : A) → north ≡ middle
  smerid : (a : A) → middle ≡ south

susp : (A : Pointed₀) → Pointed₀
susp A = (Sus (typ A) , north)

σ : {A : Type₀} → Sus A → ⋁₂susp A
σ north = north
σ south = south
σ (merid a i) = ((nmerid a) ∙ (smerid a)) i

_prim⋆_ : {A : Pointed₀} {B : Pointed₀} → (susp A →∙ B) → (susp A →∙ B) → ( ⋁₂susp (typ A) → typ B)
_prim⋆_ {A = A} {B = B} f g north = pt B
_prim⋆_ {A = A} {B = B} f g middle = pt B
_prim⋆_ {A = A} {B = B} f g south = pt B
_prim⋆_ {A = A} {B = B} f g (nmerid a i) = ((sym (snd f)) ∙ (cong (fst f) (merid a)) ∙ (cong (fst f) (sym (merid (pt A)))) ∙ (snd f)) i
_prim⋆_ {A = A} {B = B} f g (smerid a i) = ((sym (snd g)) ∙ (cong (fst g) (merid a)) ∙ (cong (fst g) (sym (merid (pt A)))) ∙ (snd g)) i

_⋆_ : {A : Pointed₀} {B : Pointed₀} → (susp A →∙ B) → (susp A →∙ B) → (susp A →∙ B)
_⋆_ {A = A} {B = B} f g = ((λ (x : typ (susp A)) → ((_prim⋆_ {A} {B} f g) (σ x))) , refl)

⋆-wellDef : {A : Pointed₀} {B : Pointed₀} {a , b , c , d : (susp A →∙ B)} → (f : a ≡ b) → (g : c ≡ d) → ((_⋆_ {A} {B} a c) ≡ (_⋆_ {A} {B} b d))
⋆-wellDef {A = A} {B = B} f g i = (_⋆_ {A} {B} (f i) (g i))

id⋆ : {A : Pointed₀} {B : Pointed₀} → (susp A →∙ B)
id⋆ {B = B} = (λ x → (pt B)) , refl

inv⋆ : {A : Pointed₀} {B : Pointed₀} → (susp A →∙ B) → (susp A →∙ B)
inv⋆ {A = A} {B = B} f = g , ((sym (cong (fst f) (merid (pt A)))) ∙ (snd f))
  where
  g : (typ (susp A))→ typ B
  g north = fst f south
  g south = fst f north
  g (merid a i) = (fst f) (merid a (~ i))

--lUnit⋆ : {A : Pointed₀} {B : Pointed₀} → (f : (susp A →∙ B)) → ( (_⋆_ {A} {B} (id⋆ {A} {B}) f) ≡ f )
--lUnit⋆ {A} {B} f i = {!!}

compSym : {A : Type₀} {a , b : A} (p : Path A a b) → (Path (Path A a a) (p ∙ (sym p)) refl)
compSym {a = a} p j i = hcomp (λ k → λ {(i = i0) → a ;
                              (i = i1) → (sym p) (j ∨ k) ;
                              (j = i1) → (a) })
                              (p (i ∧ (~ j)))

susp→loop : {A : Pointed₀} {B : Pointed₀} → (susp A →∙ B) → (A →∙ (Ω B))
susp→loop {A = A} {B = B} f = g , p
  where
    g : (typ A) → typ (Ω B)
    g a = ((sym (snd f)) ∙ (cong (fst f) (merid a))) ∙ (sym ((sym (snd f)) ∙ (cong (fst f) (merid (pt A)))))

    p : Path ((pt B) ≡ (pt B)) (g (pt A)) refl
    p = compSym {typ B} {pt B} {pt B} ((sym (snd f)) ∙ (cong (fst f) (merid (pt A))))

loop→susp : {A : Pointed₀} {B : Pointed₀}  → (A →∙ (Ω B)) → (susp A →∙ B)
loop→susp {A = A} {B = B} f = g , refl
  where
    g : typ (susp A) → typ B
    g north = pt B
    g south = pt B
    g (merid a i) = ((fst f) a) i
    
