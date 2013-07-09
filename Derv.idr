data Fn : Nat -> Nat -> Type where
    Add : Fn n m -> Fn n m -> Fn n m

    Mul : Fn n 1 -> Fn n 1 -> Fn n 1

    Exp : Fn n 1 -> Fn n 1 -> Fn n 1

    Var : (Fin n) -> Fn n 1

    Const : Float -> Fn n 1

    Tup : Vect (Fn n 1) m -> Fn n m

    Comp : Fn n m -> Fn k n -> Fn k m

    Times : Fn 2 1

    Open : String -> Fn n m

fnF : Fn 1 1
fnF = Open "f"

fnG : Fn 1 1
fnG = Open "g"

total Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect (Vect a m) n

total transpose : Matrix a n m -> Matrix a m n
transpose {n = O}     {m = O}     _   = []
transpose {n = (S k)} {m = O}     _   = []
transpose {n = O}     {m = (S k)} _   = replicate (S k) []
transpose {n = (S k)} {m = (S l)} xss = map head xss :: transpose (map tail xss)

dotWith : (a -> a -> b) -> (Vect b n -> c) -> Vect a n -> Vect a n -> c
dotWith f r xs = r . zipWith f xs

total vSum : Num a => Vect a n -> a
vSum = foldl (+) 0

total dot : Num a => Vect a n -> Vect a n -> a
dot = dotWith (*) vSum

total firstCol : Matrix a n (S m) -> Vect a n
firstCol {n = O} mat     = []
firstCol {n = (S k)} mat = map head mat

total matMul : Num a => Matrix a n m -> Matrix a m k -> Matrix a n k
matMul m1 m2 = let cols = transpose m2
               in map (\row => map (dot row) cols) m1

total mMap : (a -> b) -> Matrix a n m -> Matrix b n m
mMap f = map (map f)

instance Num (Fn n 1) where
    (+) = Add
    (*) = Mul
    x - y = Add x (Mul (Const 1) y)
    fromInteger = Const . fromInteger
    abs = believe_me

instance Num a => Num (Matrix a n m) where
    (+) = zipWith (zipWith (+))
    (-) = zipWith (zipWith (-))
    (*) = zipWith (zipWith (*))
    abs = mMap abs

-- simplify : Fn n m -> Fn n m
-- simplify (Const x) = Const x
-- simplify (Add x y) = let x' = simplify x in
--                      let y' = simplify y
--                      in case x' of
--                             Const 0.0 => believe_me x

total setAt : Fin n -> a -> Vect a n -> Vect a n
setAt fO a (x::xs)   = a :: xs
setAt (fS k) a (x::xs) = x :: setAt k a xs

deriv : Fn n m -> Matrix (Fn n 1) m n
deriv {n} (Const _)    = [replicate n (Const 0)]
deriv (Add f g)        = deriv f + deriv g
deriv {n} (Var i)      = [setAt i 1 (replicate n 0)]
deriv (Tup fs)         = ?derivTup
deriv Times            = [[Var (fS fO), Var fO]]
deriv (Comp f g)       = matMul (mMap (flip Comp g) (deriv f)) (deriv g)
-- [["D" ++  | j <- [1..n]] | i <- [1..m]]
deriv {m = O} (Open f) = []
deriv {m} {n = O} (Open f) = replicate m []
deriv {m = S k} {n = S l} (Open f) = ?mystery
-- deriv {n} {m} (Open f) = ?mystery

-- deriv {n} {m} (Open f) = 
--     where mkRow m = map (\n => "D" ++ show n ++ f ++ show m) (vectRange 1 n)
vectRangeCancellation : (a : Nat) -> (b : Nat) -> LT a b -> (S (b - (S a) + 1) = (b - a) + 1)

vectRange : (a : Nat) -> (b : Nat) -> (p : Either (a = b) (LT a b)) -> Vect Nat (b - a + 1)
vectRange a b p = case p of
    Left eqProof => ?vectRangeEqCase
    Right ltProof => ?vectRangeLtCase


total lteDecomposition : (LTE a b) -> (Either (a = b) (LT a b))
lteDecomposition {b = O}   lteZero = Left refl
lteDecomposition {b = S k} lteZero = Right (lteSucc lteZero)
lteDecomposition {a = S l} {b = S k} (lteSucc p) = case lteDecomposition p of
    Left eqProof => Left (eqSucc l k eqProof)
    Right ltProof => Right (lteSucc ltProof)


total listToVect : List a -> (p ** Vect a p)
listToVect [] = (O ** [])
listToVect (x::xs) with (listToVect xs)
    | (k ** v) = (S k ** x :: v)

ltSuccToEither : LTE (S a) b -> Either (S a = b) (LT (S a) b)
ltSuccToEither = lteDecomposition


minusEqIsZero : (a : Nat) -> (b : Nat) -> (a = b) -> (O = b - a)
minusEqIsZero O O refl = refl
minusEqIsZero (S k) (S k) refl = ?minusEqIsZeroSCase

mkRow : String -> Nat -> Nat -> Vect String n
-- mkRow f n m = map (\n => "D" ++ show n ++ f ++ show m) (getProof (listToVect [1..n]))

-- eqP : (a : Nat) -> (b : Nat) -> (S (b - (a + 1)))

finToNat' : Fin n -> Nat
finToNat' = flip finToNat O

t1 : Fn 2 1
t1 = Var fO

t2 : Fn 2 1
t2 = Var (fS fO)

t3 : Fn 1 2
t3 = Tup [Var fO, Mul 2 (Var fO)]

-- Proofs

derivTup = proof {
  intros;
  let res = concat (map deriv fs);
  rewrite (multOneRightNeutral m);
  trivial ;
}

minusEqIsZeroSCase = proof {
  intros;
  compute;
  let ih = minusEqIsZero k k refl;
  trivial;
}

vectRangeEqCase = proof {
  intros;
  compute;
  let zeroProof = minusEqIsZero a b eqProof;
  rewrite zeroProof ;
  compute;
  let res = a :: Vect.Nil;
  trivial;
}