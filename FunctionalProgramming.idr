data Day : Type where
  Monday : Day
  Tuesday : Day
  Wednesday : Day
  Thursday : Day
  Friday : Day
  Saturday : Day
  Sunday : Day

next_weekday : Day -> Day
next_weekday Monday = Tuesday
next_weekday Tuesday = Wednesday
next_weekday Wednesday = Thursday
next_weekday Thursday = Friday
next_weekday Friday = Monday
next_weekday Saturday = Monday
next_weekday Sunday = Monday

test_next_weekday : next_weekday (next_weekday Saturday) = Tuesday
test_next_weekday = Refl

data SFBool : Type where
  True : SFBool
  False : SFBool

negb : SFBool -> SFBool
negb True = False
negb False = True

andb : SFBool -> SFBool -> SFBool
andb True True = True
andb True False = False
andb False True = False
andb False False = False

orb : SFBool -> SFBool -> SFBool
orb True True = True
orb True False = True
orb False True = True
orb False False = False

test_orb1 : orb True False = True
test_orb1 = Refl

test_orb2 : orb False False = False
test_orb2 = Refl

test_orb3 : orb False True = True
test_orb3 = Refl

test_orb4 : orb True True = True
test_orb4 = Refl

nandb : SFBool -> SFBool -> SFBool
nandb True True = False
nandb True False = True
nandb False True = True
nandb False False = True

test_nandb1 : nandb True False = True
test_nandb1 = Refl

test_nandb2 : nandb False False = True
test_nandb2 = Refl

test_nandb3 : nandb False True = True
test_nandb3 = Refl

test_nandb4 : nandb True True = False
test_nandb4 = Refl

andb3 : SFBool -> SFBool -> SFBool -> SFBool
andb3 True y z = case andb y z of
                      True => True
                      False => False
andb3 False _ _ = False

test_andb31 : andb3 True True True = True
test_andb31 = Refl

test_andb32 : andb3 False True True = False
test_andb32 = Refl

test_andb33 : andb3 True False True = False
test_andb33 = Refl

test_andb34 : andb3 True True False = False
test_andb34 = Refl

data RGB : Type where
  Red : RGB
  Green : RGB
  Blue : RGB

data Color : Type where
  Black : Color
  White : Color
  Primary : RGB -> Color

monochrome : (c : Color) -> SFBool
monochrome Black = True
monochrome White = True
monochrome (Primary _) = False

is_red : (c : Color) -> SFBool
is_red (Primary Red) = True
is_red _ = False

data SFNat : Type where
  Z : SFNat
  S : SFNat -> SFNat

data SFNat' : Type where
  Stop : SFNat'
  Tick : SFNat' -> SFNat'

pred : (n : SFNat) -> SFNat
pred Z = Z
pred (S n') = n' 

minus_two : (n : SFNat) -> SFNat
minus_two Z = Z
minus_two (S Z) = Z
minus_two (S (S n')) = n'

evenb : (n : SFNat) -> SFBool
evenb Z = True
evenb (S Z) = False
evenb (S (S n')) = evenb n'

oddb : (n : SFNat) -> SFBool
oddb n = negb (evenb n)

test_oddb1 : oddb (S Z) = True
test_oddb1 = Refl

test_oddb2 : oddb (S (S (S (S Z)))) = False
test_oddb2 = Refl

plus : (n : SFNat) -> (m : SFNat) -> SFNat
plus Z m = m
plus (S n') m = S (plus n' m)

mult : (n : SFNat) -> (m : SFNat) -> SFNat
mult Z m = Z
mult (S n') m = plus m (mult n' m)

test_mult1 : Main.mult (S (S (S Z))) (S (S (S Z))) = (S (S (S (S (S (S (S (S (S Z)))))))))
test_mult1 = Refl

minus : (n : SFNat) -> (m : SFNat) -> SFNat
minus Z _ = Z
minus n Z = n
minus (S n') (S m') = minus n' m'

exp : (base : SFNat) -> (power : SFNat) -> SFNat
exp base Z = S Z
exp base (S p) = mult base (exp base p)

factorial : SFNat -> SFNat
factorial Z = S Z
factorial (S n') = mult (S n') (factorial n')

test_factorial1 : Main.factorial (S (S (S Z))) = (S (S (S (S (S (S Z))))))
test_factorial1 = Refl

test_factorial2 : Main.factorial (S (S (S (S (S Z))))) = Main.mult (S (S (S (S (S (S (S (S (S (S Z)))))))))) (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))
test_factorial2 = Refl

beq_nat : (n : SFNat) -> (m : SFNat) -> SFBool
beq_nat Z Z = True
beq_nat (S n') (S m') = beq_nat n' m' 
beq_nat _ _ = False

leb : (n : SFNat) -> (m : SFNat) -> SFBool
leb Z _ = True
leb (S n') Z = False
leb (S n') (S m') = leb n' m'

test_leb1 : leb (S (S Z)) (S (S Z)) = True
test_leb1 = Refl

test_leb2 : leb (S (S Z)) (S (S (S (S Z)))) = True
test_leb2 = Refl

test_leb3 : leb (S (S (S (S Z)))) (S (S Z)) = False
test_leb3 = Refl

blt_nat : (n : SFNat) -> (m : SFNat) -> SFBool
blt_nat n m = andb (leb n m) (negb (beq_nat n m))

test_blt_nat1 : blt_nat (S (S Z)) (S (S Z)) = False
test_blt_nat1 = Refl

test_blt_nat2 : blt_nat (S (S Z)) (S (S (S (S Z)))) = True
test_blt_nat2 = Refl

test_blt_nat3 : blt_nat (S (S (S (S Z)))) (S (S Z)) = False
test_blt_nat3 = Refl

plus_0_n : Main.plus Z n = n
plus_0_n = Refl

plus_1_1 : Main.plus (S Z) n = S n
plus_1_1 = Refl

mult_0_1 : Main.mult Z n = Z
mult_0_1 = Refl

plus_id_exercise : n = m -> m = o -> Main.plus n m = Main.plus m o
plus_id_exercise Refl Refl = Refl

mult_0_plus : Main.mult (Main.plus Z n) m = Main.mult n m
mult_0_plus = Refl

mult_S_1 : m = S n -> Main.mult m (Main.plus (S Z) n) = Main.mult m m
mult_S_1 Refl = Refl

plus_1_neq_0 : beq_nat (Main.plus (S Z) n) Z = False
plus_1_neq_0 = Refl

negb_involutive : negb (negb b) = b
negb_involutive {b = True} = Refl
negb_involutive {b = False} = Refl

andb_commutative : andb b c = andb c b
andb_commutative {b = True} {c = True} = Refl
andb_commutative {b = True} {c = False} = Refl
andb_commutative {b = False} {c = True} = Refl
andb_commutative {b = False} {c = False} = Refl

andb3_exchange : andb (andb b c) d = andb b (andb c d)
andb3_exchange {b = True} {c = True} {d = True} = Refl
andb3_exchange {b = True} {c = True} {d = False} = Refl
andb3_exchange {b = True} {c = False} {d = True} = Refl
andb3_exchange {b = True} {c = False} {d = False} = Refl
andb3_exchange {b = False} {c = True} {d = True} = Refl
andb3_exchange {b = False} {c = False} {d = True} = Refl
andb3_exchange {b = False} {c = True} {d = False} = Refl
andb3_exchange {b = False} {c = False} {d = False} = Refl

andb_true_elim2 : andb b c = True -> c = True
andb_true_elim2 {b = True} {c = True} Refl = Refl
andb_true_elim2 {b = True} {c = False} Refl impossible
andb_true_elim2 {b = False} {c = True} Refl impossible
andb_true_elim2 {b = False} {c = False} Refl impossible

zero_nbeq_plus_1 : beq_nat Z (Main.plus (S Z) n) = False
zero_nbeq_plus_1 = Refl

identity_fn_applied_twice : {f : SFBool -> SFBool} -> f b = b -> f (f b) = b
identity_fn_applied_twice prf = rewrite prf in rewrite prf in Refl

andb_eq_orb : andb b c = orb b c -> b = c
andb_eq_orb {b = True} {c = True} Refl = Refl
andb_eq_orb {b = False} {c = False} Refl = Refl
andb_eq_orb {b = True} {c = False} Refl impossible
andb_eq_orb {b = False} {c = True} Refl impossible

data Binary : Type where
  BZ : Binary
  Twice : Binary -> Binary
  TwicePlusOne : Binary -> Binary

incr : Binary -> Binary
incr BZ = TwicePlusOne BZ
incr (Twice b) = TwicePlusOne b
incr (TwicePlusOne b) = Twice (incr b)

bin_to_nat : Binary -> SFNat
bin_to_nat BZ = Z
bin_to_nat (Twice b) = Main.mult (S (S Z)) (bin_to_nat b)
bin_to_nat (TwicePlusOne b) = Main.plus (Main.mult (S (S Z)) (bin_to_nat b)) (S Z)

test_bin_incr1 : bin_to_nat (incr BZ) = S Z
test_bin_incr1 = Refl

test_bin_incr2 : bin_to_nat (incr BZ) = S (bin_to_nat BZ)
test_bin_incr2 = Refl

test_bin_incr3 : bin_to_nat (incr (Twice (TwicePlusOne BZ))) = S (S (S Z))
test_bin_incr3 = Refl

test_bin_incr4 : bin_to_nat (incr (Twice (Twice BZ))) = S Z
test_bin_incr4 = Refl

test_bin_incr5 : bin_to_nat (incr (TwicePlusOne (Twice BZ))) = S (S Z)
test_bin_incr5 = Refl
