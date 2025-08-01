open import Prelude

open import Order.Base
open import Order.Strict
open import Order.Trichotomous

open import Data.Empty
open import Data.Nat.Properties
open import Data.Nat.Order.Base renaming ( _<_ to _<ⁿ_ ; <-trans to <ⁿ-trans ; <-asym to <ⁿ-asym       ; <→≠ to <ⁿ→≠
                                         ; _≤_ to _≤ⁿ_ ; ≤-trans to ≤ⁿ-trans ; ≤-antisym to ≤ⁿ-antisym ; ≤-refl to ≤ⁿ-refl)
open import Data.Bool renaming (elim to elimᵇ ; rec to recᵇ)
open import Data.Maybe renaming (elim to elimᵐ ; rec to recᵐ ; ∈-map to ∈-mapᵐ)
open import Data.Dec
open import Data.Reflects
open import Data.Dec.Tri renaming (elim to elimᵗ ; rec to recᵗ)
open import Data.Acc

open import Data.List
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.At
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Binary.Perm
open import Data.List.Correspondences.Binary.OPE

import KVList

module KVList.Ord
  {ℓᵏ ℓᵛ ℓ ℓ′ : Level}
  {K< : StrictPoset ℓᵏ ℓ}
  {V≤ : Poset ℓᵛ ℓ′}
  ⦃ d : is-trichotomous K< ⦄  -- TODO move this down

  where

  open StrictPoset K< renaming (Ob to K)
  open Poset V≤ renaming (Ob to V)
  open is-trichotomous d hiding (Ob ; _<_ ; <-asym ; <-trans ; <→≠)
  open KVList {K< = K<} {V}
  open KVList.Ops {K< = K<} {V = V}

  data _≤kv_ : List (K × V) → List (K × V) → 𝒰 (ℓᵏ ⊔ ℓᵛ ⊔ ℓ′) where
    kvdone : [] ≤kv []
    kvtake : ∀ {kx ky vx vy xs ys}
           → kx ＝ ky → vx ≤ vy → xs ≤kv ys
           → ((kx , vx) ∷ xs) ≤kv ((ky , vy) ∷ ys)
    kvdrop : ∀ {xs ky vy ys}
           → xs ≤kv ys
           → xs ≤kv ((ky , vy) ∷ ys)

  KV≤-length : {xs ys : List (K × V)} → xs ≤kv ys → length xs ≤ⁿ length ys
  KV≤-length  kvdone        = z≤
  KV≤-length (kvtake _ _ l) = s≤s (KV≤-length l)
  KV≤-length (kvdrop l)     = ≤ⁿ-trans (KV≤-length l) ≤-ascend

  KV≤-init : {xs : List (K × V)} → [] ≤kv xs
  KV≤-init {xs = []}           = kvdone
  KV≤-init {xs = (k , v) ∷ xs} = kvdrop KV≤-init

  KV≤-refl : {xs : List (K × V)} → xs ≤kv xs
  KV≤-refl {xs = []}           = kvdone
  KV≤-refl {xs = (k , v) ∷ xs} = kvtake refl refl KV≤-refl

  KV≤-trans : {xs ys zs : List (K × V)} → xs ≤kv ys → ys ≤kv zs → xs ≤kv zs
  KV≤-trans  xy                  kvdone             = xy
  KV≤-trans (kvtake exy lxy xy) (kvtake eyz lyz yz) = kvtake (exy ∙ eyz) (lxy ∙ lyz) (KV≤-trans xy yz)
  KV≤-trans (kvdrop xy)         (kvtake _ _ yz)     = kvdrop (KV≤-trans xy yz)
  KV≤-trans  xy                 (kvdrop yz)         = kvdrop (KV≤-trans xy yz)

  KV≤-antisym : {xs ys : List (K × V)} → xs ≤kv ys → ys ≤kv xs → xs ＝ ys
  KV≤-antisym  kvdone          _               = refl
  KV≤-antisym (kvtake e l xy) (kvtake _ l′ yx) =
    ap² {C = λ _ _ → List (K × V)} _∷_ (×-path e (≤-antisym l l′)) (KV≤-antisym xy yx)
  KV≤-antisym (kvtake _ _ xy) (kvdrop yx)      =
    false! (≤ⁿ-trans (KV≤-length yx) (KV≤-length xy))
  KV≤-antisym (kvdrop xy)     (kvtake _ _ yx)  =
    false! (≤ⁿ-trans (KV≤-length xy) (KV≤-length yx))
  KV≤-antisym (kvdrop xy)     (kvdrop yx)      =
    false! $ ≤≃≤+r {n = 2} ⁻¹ $ ≤ⁿ-trans (s≤s $ KV≤-length xy) (KV≤-length yx)

  -- alternative definition via lookup
  Is-submap : List (K × V) → List (K × V) → 𝒰 (ℓᵏ ⊔ ℓᵛ ⊔ ℓ′)
  Is-submap xs ys = All (λ where (kx , vx) →
                                   Σ[ vy ꞉ V ] (lookup-kv kx ys ＝ just vy) × (vx ≤ vy)) -- TODO ∃ ?
                        xs

  KV≤→sub : {xs ys : List (K × V)}
          → Is-kvlist ys
          → xs ≤kv ys
          → Is-submap xs ys
  KV≤→sub {xs = .[]}            {ys = .[]}             _       kvdone                                         = []
  KV≤→sub {xs = (kx , vx) ∷ xs} {ys = (ky , vy) ∷ ys} (∷ˢ ry) (kvtake {kx} {ky} {vx} {vy} {xs} {ys} ex lx le) =
    ( vy
    , given-eq ex
        return (λ q → recᵗ nothing (just vy) (lookup-kv kx ys) q ＝ just vy)
        then refl
    , lx)
    ∷ all-map
        (λ {x} → λ where
             (vy′ , ey′ , le′) →
                 vy′
               , given-gt All→∀∈ (related→all ry) (x .fst) (lookup→has ey′)
                   return (λ q → recᵗ nothing (just vy) (lookup-kv (x .fst) ys) q ＝ just vy′)
                   then ey′
               , le′)
        (KV≤→sub (related→sorted ry) le)
  KV≤→sub {xs = xs}             {ys = (ky , vy) ∷ ys} (∷ˢ ry) (kvdrop {xs} {ky} {vy} {ys} le)                 =
    all-map
      (λ {x} → λ where
             (vy′ , ey′ , le′) →
                  vy′
                , (given-gt All→∀∈ (related→all ry) (x .fst) (lookup→has ey′)
                   return (λ q → recᵗ nothing (just vy) (lookup-kv (x .fst) ys) q ＝ just vy′)
                   then ey′)
                , le′)
      (KV≤→sub (related→sorted ry) le)

  sub→KV≤ : {xs ys : List (K × V)}
          → Is-kvlist xs
          → Is-submap xs ys
          → xs ≤kv ys
  sub→KV≤ {xs = []}                                    _       []                   = KV≤-init
  sub→KV≤ {xs = (kx , vx) ∷ xs} {ys = []}              _      ((vy  , ey , ly) ∷ a) = false! ey
  sub→KV≤ {xs = (kx , vx) ∷ xs} {ys = (ky , vy) ∷ ys} (∷ˢ rx) ((vy′ , ey , ly) ∷ a) with trisect kx ky
  ... | LT x<y = false! ey
  ... | EQ x=y = kvtake x=y
                        (subst (vx ≤_) (just-inj ey ⁻¹) ly)
                        (sub→KV≤ (related→sorted rx)
                                 (all-∈-map (λ {x} hx → λ where
                                                             (vy″ , ey″ , ly″) →
                                                                  vy″
                                                                , (given-gt subst (_< x .fst) x=y $ All→∀∈ (related→all rx) (x .fst) (∈-map fst hx)
                                                                     return (λ q → recᵗ nothing (just vy) (lookup-kv (x .fst) ys) q ＝ just vy″ → lookup-kv (x .fst) ys ＝ just vy″)
                                                                     then id) ey″
                                                                , ly″)
                                     a))
  ... | GT y<x = kvdrop (sub→KV≤ (∷ˢ rx)
                                 ((vy′ , (ey , ly))
                                  ∷ all-∈-map (λ {x} hx → λ where
                                                               (vy″ , ey″ , ly″) →
                                                                    vy″
                                                                  , (given-gt y<x ∙ All→∀∈ (related→all rx) (x .fst) (∈-map fst hx)
                                                                       return (λ q → recᵗ nothing (just vy) (lookup-kv (x .fst) ys) q ＝ just vy″ → lookup-kv (x .fst) ys ＝ just vy″)
                                                                       then id) ey″
                                                                  , ly″)
                                      a))

  KV≤-prop : {xs ys : List (K × V)}
           → Is-kvlist ys
           → is-prop (xs ≤kv ys)
  KV≤-prop  _       kvdone             kvdone            = refl
  KV≤-prop (∷ˢ ry) (kvtake e₁ l₁ xy₁) (kvtake e₂ l₂ xy₂) =
      ap² (λ x y → kvtake x y xy₁) (is-discrete→is-set (tri-order→discrete d) _ _ e₁ e₂) (≤-thin l₁ l₂)
    ∙ ap (kvtake e₂ l₂) (KV≤-prop (related→sorted ry) xy₁ xy₂)
  KV≤-prop (∷ˢ ry) (kvtake e₁ l₁ xy₁) (kvdrop xy₂)       =
    let vel = all-head $ KV≤→sub (related→sorted ry) xy₂
        lt = All→∀∈ (related→all ry) _ (lookup→has (vel .snd .fst))
      in
    absurd (<→≠ lt (e₁ ⁻¹))
  KV≤-prop (∷ˢ ry) (kvdrop xy₁)       (kvtake e₂ l₂ xy₂) =
    let vel = all-head $ KV≤→sub (related→sorted ry) xy₁
        lt = All→∀∈ (related→all ry) _ (lookup→has (vel .snd .fst))
      in
    absurd (<→≠ lt (e₂ ⁻¹))
  KV≤-prop (∷ˢ ry) (kvdrop xy₁)       (kvdrop xy₂)       =
    ap kvdrop (KV≤-prop (related→sorted ry) xy₁ xy₂)

  -- upsert

  upsert-≤ : {f : V → V → V} {k : K} {v : V} {xs : List (K × V)}
           → (∀ x → x ≤ f x v)
           → xs ≤kv upsert-kv f k v xs
  upsert-≤         {xs = []}             fle = KV≤-init
  upsert-≤ {k} {v} {xs = (kx , vx) ∷ xs} fle with trisect k kx
  ... | LT _ = kvdrop KV≤-refl
  ... | EQ e = kvtake (e ⁻¹) (fle vx) KV≤-refl
  ... | GT _ = kvtake refl ≤-refl (upsert-≤ fle)

  -- remove

  remove-≤ : {k : K} {xs : List (K × V)} → remove-kv k xs ≤kv xs
  remove-≤     {xs = []}             = kvdone
  remove-≤ {k} {xs = (kx , vx) ∷ xs} with trisect k kx
  ... | LT _ = KV≤-refl
  ... | EQ _ = kvdrop KV≤-refl
  ... | GT _ = kvtake refl refl remove-≤

  -- union

  union-≤-lr-aux : {f : V → V → V} (xs ys : List (K × V))
                 → (∀ x y → (x ≤ f x y) × (y ≤ f x y))
                 → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                 → (xs ≤kv union-kv f xs ys) × (ys ≤kv union-kv f xs ys)
  union-≤-lr-aux      []               _               _    _        = KV≤-init , KV≤-refl
  union-≤-lr-aux     ((kx , vx) ∷ xs)  []              _    _        = KV≤-refl , KV≤-init
  union-≤-lr-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) fle (acc rec) with trisect kx ky
  ... | LT x<y =
    let (ihl , ihr) = union-≤-lr-aux {f = f} xs ((ky , vy) ∷ ys)
                                     fle
                                     (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
      in
    kvtake refl refl ihl , kvdrop ihr
  ... | EQ x=y =
    let (ihl , ihr) = union-≤-lr-aux {f = f} xs ys
                                     fle
                                     (rec (xs ++ ys) (<-suc-r (subst (length (xs ++ ys) <ⁿ_)
                                                             (  ap suc (++-length xs ys)
                                                              ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                              ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                             <-ascend)))
        (fl , fr) = fle vx vy
      in
    kvtake refl fl ihl , kvtake (x=y ⁻¹) fr ihr
  ... | GT y<x =
    let (ihl , ihr) = union-≤-lr-aux {f = f} ((kx , vx) ∷ xs) ys
                                     fle
                                     (rec (((kx , vx) ∷ xs) ++ ys)
                                          (s<s (subst (length (xs ++ ys) <ⁿ_)
                                                      (  ap suc (++-length xs ys)
                                                       ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                       ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                      <-ascend)))
      in
    kvdrop ihl , kvtake refl refl ihr

  union-≤-lr : {f : V → V → V} {xs ys : List (K × V)}
             → (∀ x y → (x ≤ f x y) × (y ≤ f x y))
             → (xs ≤kv union-kv f xs ys) × (ys ≤kv union-kv f xs ys)
  union-≤-lr {f} {xs} {ys} fle = union-≤-lr-aux {f = f} xs ys fle (acc-lift length (xs ++ ys) (<-is-wf (length (xs ++ ys))))

  union-≤-least : {f : V → V → V} (xs ys ub : List (K × V))
                → Is-kvlist ub
                → (∀ x y z → x ≤ z → y ≤ z → f x y ≤ z)
                → xs ≤kv ub → ys ≤kv ub → union-kv f xs ys ≤kv ub
  union-≤-least     []                ys               ub               _      _    xle                yle               = yle
  union-≤-least     (_ ∷ _)           []               ub               _      _    xle                yle               = xle
  union-≤-least {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) ((ku , vu) ∷ ub) (∷ˢ ru) fle (kvtake ex lx xle) (kvtake ey ly yle) =
    given-eq (ex ∙ ey ⁻¹)
      return (λ q → recᵗ ((kx , vx) ∷ union-kv f xs ((ky , vy) ∷ ys))
                         ((kx , f vx vy) ∷ union-kv f xs ys)
                         ((ky , vy) ∷ union-kv f ((kx , vx) ∷ xs) ys)
                         q ≤kv ((ku , vu) ∷ ub))
      then kvtake ex (fle vx vy vu lx ly)
              (union-≤-least xs ys ub
                  (related→sorted ru)
                  fle xle yle)
  union-≤-least {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) ((ku , vu) ∷ ub) (∷ˢ ru) fle (kvtake ex lx xle) (kvdrop yle)       =
    let vel = all-head $ KV≤→sub (related→sorted ru) yle
        lu = All→∀∈ (related→all ru) ky (lookup→has (vel .snd .fst))
      in
    given-lt subst (_< ky) (ex ⁻¹) lu
       return (λ q → recᵗ ((kx , vx) ∷ union-kv f xs ((ky , vy) ∷ ys))
                          ((kx , f vx vy) ∷ union-kv f xs ys)
                          ((ky , vy) ∷ union-kv f ((kx , vx) ∷ xs) ys)
                          q ≤kv ((ku , vu) ∷ ub))
       then kvtake ex lx
               (union-≤-least xs ((ky , vy) ∷ ys) ub
                 (related→sorted ru)
                 fle xle yle)
  union-≤-least {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) ((ku , vu) ∷ ub) (∷ˢ ru) fle (kvdrop xle)       (kvtake ey ly yle) =
    let vel = all-head $ KV≤→sub (related→sorted ru) xle
        lu = All→∀∈ (related→all ru) kx (lookup→has (vel .snd .fst))
      in
    given-gt subst (_< kx) (ey ⁻¹) lu
       return (λ q → recᵗ ((kx , vx) ∷ union-kv f xs ((ky , vy) ∷ ys))
                          ((kx , f vx vy) ∷ union-kv f xs ys)
                          ((ky , vy) ∷ union-kv f ((kx , vx) ∷ xs) ys)
                          q ≤kv ((ku , vu) ∷ ub))
       then kvtake ey ly
              (union-≤-least ((kx , vx) ∷ xs) ys ub
                 (related→sorted ru)
                 fle xle yle)
  union-≤-least {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) ((ku , vu) ∷ ub) (∷ˢ ru) fle (kvdrop xle)       (kvdrop yle)       =
    (caseᵗ kx >=< ky
      return (λ q → recᵗ ((kx , vx) ∷ union-kv (λ z z₁ → f z z₁) xs ((ky , vy) ∷ ys))
                         ((kx , f vx vy) ∷ union-kv (λ z z₁ → f z z₁) xs ys)
                         ((ky , vy) ∷ union-kv (λ z z₁ → f z z₁) ((kx , vx) ∷ xs) ys)
                         q ≤kv ub
                  → recᵗ ((kx , vx) ∷ union-kv f xs ((ky , vy) ∷ ys))
                         ((kx , f vx vy) ∷ union-kv f xs ys)
                         ((ky , vy) ∷ union-kv f ((kx , vx) ∷ xs) ys)
                         q ≤kv ((ku , vu) ∷ ub))
      of λ where
             (LT x<y) → kvdrop
             (EQ x=y) → kvdrop
             (GT y<x) → kvdrop)
      (union-≤-least ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) ub
                 (related→sorted ru)
                 fle xle yle)

  -- inter

  inter-≤-lr-aux : {f : V → V → V} (xs ys : List (K × V))
                 → (∀ x y → (f x y ≤ x) × (f x y ≤ y))
                 → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                 → (inter-kv f xs ys ≤kv xs) × (inter-kv f xs ys ≤kv ys)
  inter-≤-lr-aux     []                ys              fle ac        = kvdone , KV≤-init
  inter-≤-lr-aux     (_ ∷ _)           []              fle ac        = KV≤-init , kvdone
  inter-≤-lr-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) fle (acc rec) with trisect kx ky
  ... | LT x<y =
    let (ihl , ihr) = inter-≤-lr-aux {f = f} xs ((ky , vy) ∷ ys)
                                     fle
                                     (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
      in
    kvdrop ihl , ihr
  ... | EQ x=y =
    let (ihl , ihr) = inter-≤-lr-aux {f = f} xs ys
                                     fle
                                     (rec (xs ++ ys) (<-suc-r (subst (length (xs ++ ys) <ⁿ_)
                                                             (  ap suc (++-length xs ys)
                                                              ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                              ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                             <-ascend)))
        (fl , fr) = fle vx vy
      in
    kvtake refl fl ihl , kvtake x=y fr ihr
  ... | GT y<x =
    let (ihl , ihr) = inter-≤-lr-aux {f = f} ((kx , vx) ∷ xs) ys
                                     fle
                                     (rec (((kx , vx) ∷ xs) ++ ys)
                                          (s<s (subst (length (xs ++ ys) <ⁿ_)
                                                      (  ap suc (++-length xs ys)
                                                       ∙ +-suc-r (length xs) (length ys) ⁻¹
                                                       ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                                      <-ascend)))
      in
    ihl , kvdrop ihr

  inter-≤-lr : {f : V → V → V} {xs ys : List (K × V)}
             → (∀ x y → (f x y ≤ x) × (f x y ≤ y))
             → (inter-kv f xs ys ≤kv xs) × (inter-kv f xs ys ≤kv ys)
  inter-≤-lr {f} {xs} {ys} fle = inter-≤-lr-aux {f = f} xs ys fle (acc-lift length (xs ++ ys) (<-is-wf (length (xs ++ ys))))

  inter-≤-greatest-aux : {f : V → V → V} (xs ys lb : List (K × V))
                       → Acc (λ x y → length x <ⁿ length y) (xs ++ ys)
                       → Is-kvlist xs → Is-kvlist ys
                       → (∀ x y z → z ≤ x → z ≤ y → z ≤ f x y)
                       → lb ≤kv xs → lb ≤kv ys → lb ≤kv inter-kv f xs ys
  inter-≤-greatest-aux      []               ys                lb              _          _      _       _    xle                                              _                                               = xle
  inter-≤-greatest-aux      (_ ∷ _)          []                lb              _          _       _      _    _                                                yle                                             = yle
  inter-≤-greatest-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) .((kl , vl) ∷ lb) (acc rec) (∷ˢ rx) (∷ˢ ry) fle (kvtake {kx = kl} {vx = vl} {xs = lb} ex lx xle) (kvtake ey ly yle)                               =
    given-eq (ex ⁻¹ ∙ ey)
      return (λ q → ((kl , vl) ∷ lb) ≤kv recᵗ (inter-kv f xs ((ky , vy) ∷ ys))
                                              ((kx , f vx vy) ∷ inter-kv f xs ys)
                                              (inter-kv f ((kx , vx) ∷ xs) ys)
                                              q)
      then kvtake ex (fle vx vy vl lx ly)
             (inter-≤-greatest-aux xs ys lb
                 (rec (xs ++ ys)
                      (<-suc-r $
                       subst (length (xs ++ ys) <ⁿ_)
                             (  ap suc (++-length xs ys)
                              ∙ +-suc-r (length xs) (length ys) ⁻¹
                              ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                             <-ascend))
                 (related→sorted rx) (related→sorted ry)
                 fle xle yle)
  inter-≤-greatest-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) .((kl , vl) ∷ lb) (acc rec) (∷ˢ rx) (∷ˢ ry) fle (kvtake {kx = kl} {vx = vl} {xs = lb} ex lx xle) (kvdrop yle)                                     =
    let vel = all-head $ KV≤→sub (related→sorted ry) yle
        ll = All→∀∈ (related→all ry) kl (lookup→has (vel .snd .fst))
      in
    given-gt subst (ky <_) ex ll
       return (λ q → ((kl , vl) ∷ lb) ≤kv recᵗ (inter-kv f xs ((ky , vy) ∷ ys))
                                               ((kx , f vx vy) ∷ inter-kv f xs ys)
                                               (inter-kv f ((kx , vx) ∷ xs) ys)
                                               q)
       then inter-≤-greatest-aux ((kx , vx) ∷ xs) ys ((kl , vl) ∷ lb)
               (rec ((kx , vx) ∷ xs ++ ys)
                    (s<s $
                     subst (length (xs ++ ys) <ⁿ_)
                           (  ap suc (++-length xs ys)
                            ∙ +-suc-r (length xs) (length ys) ⁻¹
                            ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                           <-ascend))
               (∷ˢ rx) (related→sorted ry)
               fle (kvtake ex lx xle) yle
  inter-≤-greatest-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys) .((kl , vl) ∷ lb) (acc rec) (∷ˢ rx) (∷ˢ ry) fle (kvdrop xle)                                     (kvtake {kx = kl} {vx = vl} {xs = lb} ey ly yle) =
    let vel = all-head $ KV≤→sub (related→sorted rx) xle
        ll = All→∀∈ (related→all rx) kl (lookup→has (vel .snd .fst))
      in
    given-lt subst (kx <_) ey ll
       return (λ q → ((kl , vl) ∷ lb) ≤kv recᵗ (inter-kv f xs ((ky , vy) ∷ ys))
                                               ((kx , f vx vy) ∷ inter-kv f xs ys)
                                               (inter-kv f ((kx , vx) ∷ xs) ys)
                                               q)
       then inter-≤-greatest-aux xs ((ky , vy) ∷ ys) ((kl , vl) ∷ lb)
              (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
              (related→sorted rx) (∷ˢ ry)
              fle xle (kvtake ey ly yle)
  inter-≤-greatest-aux {f} ((kx , vx) ∷ xs) ((ky , vy) ∷ ys)   lb              (acc rec) (∷ˢ rx) (∷ˢ ry) fle (kvdrop xle)                                     (kvdrop yle)                                     with trisect kx ky
  ... | LT x<y = inter-≤-greatest-aux xs ((ky , vy) ∷ ys) lb
                   (rec (xs ++ (ky , vy) ∷ ys) <-ascend)
                   (related→sorted rx) (∷ˢ ry)
                   fle xle (kvdrop yle)
  ... | EQ x=y = kvdrop $ inter-≤-greatest-aux xs ys lb
                             (rec (xs ++ ys)
                                  (<-suc-r $
                                   subst (length (xs ++ ys) <ⁿ_)
                                         (  ap suc (++-length xs ys)
                                          ∙ +-suc-r (length xs) (length ys) ⁻¹
                                          ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                                         <-ascend))
                             (related→sorted rx) (related→sorted ry)
                             fle xle yle
  ... | GT y<x = inter-≤-greatest-aux ((kx , vx) ∷ xs) ys lb
                   (rec ((kx , vx) ∷ xs ++ ys)
                        (s<s $
                         subst (length (xs ++ ys) <ⁿ_)
                               (  ap suc (++-length xs ys)
                                ∙ +-suc-r (length xs) (length ys) ⁻¹
                                ∙ ++-length xs ((ky , vy) ∷ ys) ⁻¹ )
                               <-ascend))
                   (∷ˢ rx) (related→sorted ry)
                   fle (kvdrop xle) yle

  inter-≤-greatest : {f : V → V → V} {xs ys lb : List (K × V)}
                   → Is-kvlist xs → Is-kvlist ys
                   → (∀ x y z → z ≤ x → z ≤ y → z ≤ f x y)
                   → lb ≤kv xs → lb ≤kv ys → lb ≤kv inter-kv f xs ys
  inter-≤-greatest {f} {xs} {ys} {lb} =
    inter-≤-greatest-aux {f} xs ys lb (acc-lift length (xs ++ ys) (<-is-wf (length (xs ++ ys))))
