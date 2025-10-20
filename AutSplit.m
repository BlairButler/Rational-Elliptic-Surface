// Return a scalar and the new minimal polynomial s.t, the scaled roots of f are algebraic integers
//
// More effort compared to GaloisGroup -- we hope for a smaller scaler

verbose := true;

function find_scale(f)
 mul := LCM([Denominator(a) : a in Coefficients(f)]);
 f := f * mul;
 f := f / GCD([Integers()!a : a in Coefficients(f)]);
 lc := LeadingCoefficient(f);
 if lc lt 0 then f := -f; end if;
 lc := Integers()!LeadingCoefficient(f);
 assert lc gt 0;
 assert lc in Integers();
 if lc eq 1 then return 1,f; end if;
 scale := 1;
 co := [Integers()!a : a in Coefficients(f)];
 bas := CoprimeBasis(co);
 bas := [a[1] : a in bas];
 for fac in bas do
  act := Gcd(lc,fac);
  if act gt 1 and act lt 10^500 then
   e1,e2 := TrialDivision(act:Proof := false);
   for a in e1 do
    p := a[1];
    vl := [Valuation(c,p) : c in co];
    ex := (Min([(vl[i] - vl[#vl]) / (#vl-i) : i in [1..#vl-1]]));
    ex :=Ceiling(-ex);
    scale := scale * p^ex;
   end for;
   for a in e2 do
    scale := scale * a;
   end for;
  else
   scale := scale * act;
  end if;
 end for;
 co := [(co[i]*scale^(#co - i)) : i in [1..#co]];
 ggt := Gcd(co);
 co := [a div ggt : a in co];
 return scale, Polynomial(co);
end function;


/* Given a list of polynomials,
   We compute a splitting field, its automorphism group and the roots of the initial polynomials in the splitting field
*/
function SplitAutGrp(fl:Prime := false)
 prod := &*fl;
 assert IsSquarefree(prod); // Non
 assert FieldOfFractions(BaseRing(Parent(prod))) eq Rationals(); // Only abolute number fields are supported
 scale, pol := find_scale(prod);
 fl_scaled := [Evaluate(f,Parent(f).1/scale) : f in fl];
 fl_scaled := [f * LCM([Denominator(b) : b in Coefficients(f)]) : f in fl_scaled]; 
 rz := PolynomialRing(Integers());
 fl_scaled := [rz!a : a in fl_scaled];
 if verbose then printf"Calling Galois group.\n"; end if;
// SetVerbose("Subfields",0);
 G,r,S := GaloisGroup(pol:Prime := Prime);
// SetVerbose("Subfields",3);
 
 p := S`Prime;

 if verbose then printf"Computing defining polynomial of splitting field.\n"; end if; 
 big_f, inv, tschirn := GaloisSubgroup(S,sub<G | >);
 assert Discriminant(PolynomialRing(GF(p))!big_f) ne 0; // Wrong prime!
 nf := NumberField(big_f);
 ord := EquationOrder(nf);
 mul := Evaluate(Derivative(big_f),nf.1);
 mul_inv := mul^(-1);
 if verbose then printf"Building GaloisData of splitting field.\n"; end if; 
 S2 := GaloisData(nf: Prime := p, CollectShapes := false);
 S2`Ring := S`Ring;
 phi,G2 := CosetAction(G, sub<G | >);
 r_tschirn := [Evaluate(tschirn, GaloisRoot(i,S:Prec := 5)) : i in [1..Degree(prod)]];
 S2`Roots := [-Evaluate(inv^(i @@ phi), r_tschirn) : i in [1..Degree(big_f)]];
 if verbose then printf"Building automorphism group.\n"; end if;
 aut,aut_map := GaloisAutomorphismGroup(nf: Galois := <G2,S2`Roots,S2>);

 if verbose then printf"Computing roots of initial polynomial in the splitting field.\n"; end if; 
  lift_bound := 2*FujiwaraBound(pol) * Degree(pol) * Degree(big_f) * 
               Sqrt(&+[a^2  : a in Coefficients(big_f)]);
 max_lift_prec := Ceiling(Log(lift_bound) / Log(p));

 root_ll := [[] : f in fl];
 kp := ResidueClassField(S`Ring);
 xl := [kp!GaloisRoot(j,S2) : j in [1..Degree(big_f)]];
 for i := 1 to Degree(G) do
  ind_l := [k : k in [1..#fl] | IsWeaklyZero(Evaluate(fl_scaled[k],GaloisRoot(i,S)))]; 
  assert #ind_l eq 1;
  k := ind_l[1]; 
  
  wl := [kp!GaloisRoot(i^(j @@ phi),S) : j in [1..Degree(big_f)]];
  emb := ord!Evaluate(PolynomialRing(Integers())!(Interpolation(xl,wl)), nf.1);

  if verbose then printf"Calling lift, MaxPrec = %o\n", max_lift_prec; end if;
  suc, e1,e2 := InternalLiftEmbeddingANF(ord!(emb*mul), p, ord, fl_scaled[k], mul, mul_inv : MaxPrec := max_lift_prec, Pretest := true);
  assert suc;
  Append(~root_ll[k],e2 / scale);
 end for;
 
 return nf, aut, aut_map, root_ll; 
end function; 


/* Test Examples:

// small
q<x> := PolynomialRing(Rationals());
fl := [PolynomialWithGaloisGroup(4,1), PolynomialWithGaloisGroup(3,2)];
time e1,e2,e3,e4 := SplitAutGrp(fl);
[[Evaluate(fl[i],a) : a in e4[i]] : i in [1..#fl]];

// medium
q<x> := PolynomialRing(Rationals());
fl := [PolynomialWithGaloisGroup(3,2), PolynomialWithGaloisGroup(2,1), PolynomialWithGaloisGroup(5,2)];
time e1,e2,e3,e4 := SplitAutGrp(fl:Prime := NextPrime(10^6));
[[Evaluate(fl[i],a) : a in e4[i]] : i in [1..#fl]];

// large
q<x> := PolynomialRing(Rationals());
fl := [
    x^2 - x + 1,
    x^40 + 2002*x^30 - 8910209/1080*x^20 + 76483/675*x^10 + 1/583200000,
    x^60 + 2002*x^45 - 8910209/1080*x^30 + 76483/675*x^15 + 1/583200000
];
time e1,e2,e3,e4 := SplitAutGrp(fl:Prime := NextPrime(10^6));
[[Evaluate(fl[i],a) : a in e4[i]] : i in [1..#fl]];


fl := [
    x^24 - 456601500*x^18 - 428631250*x^12 + 520312500*x^6 + 9765625,
    x^16 - 456601500*x^12 - 428631250*x^8 + 520312500*x^4 + 9765625,
    x^4 + x^3 + x^2 + x + 1,
    x^2 - x + 1
];
time e1,e2,e3,e4 := SplitAutGrp(fl:Prime := NextPrime(10^6));
[[Evaluate(fl[i],a) : a in e4[i]] : i in [1..#fl]];

fl := [
    x^40 + 91188840960*x^30 + 18085024812736512/5*x^20 - 
        43047258401846329344/25*x^10 + 6499837226778624/3125,
    x^12 + 76*x^9 - 48*x^6 - 320*x^3 - 256/5,
    x^8 + 72*x^6 - 270*x^4 + 729/5,
    x^2 - x + 1
];
time e1,e2,e3,e4 := SplitAutGrp(fl:Prime := NextPrime(10^6));
[[Evaluate(fl[i],a) : a in e4[i]] : i in [1..#fl]];



*/

