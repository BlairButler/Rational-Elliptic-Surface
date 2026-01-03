/*When on Toby*/
Attach("/home/blair/+IdealsNF.m");
Attach("/home/blair/Subfields.m");
Attach("/home/blair/Galois.m");
Attach("/home/blair/GalAuto.m");
Attach("/home/blair/Invar.m");



Attach("AutSplit.m");

_<t>:=FunctionField(Rationals());
E:=EllipticCurve([0,t^4+t^2]);


function RationalEllipticSurface(E);

_<[a]> := PolynomialRing(Rationals(),7);
_<tt> := PolynomialRing(Universe(a));
x := a[1]*tt^2 + a[2]*tt + a[3];
y := a[4]*tt^3 + a[5]*tt^2 + a[6]*tt + a[7];
ftmap:=hom<Parent(t) -> Parent(tt)| tt>;
coor:=[Parent(x)!ftmap(Coefficients(E))[i] : i in [1..5] ];
cfs:= Coefficients(y^2 + coor[1]*x*y + coor[3]*y -x^3 - coor[2]*x^2-coor[4]*x-coor[5]);
I:=ideal<Universe(a) | cfs>;
_,P:=PrimaryDecomposition(I);
//X := Cluster(AffineSpace(Universe(a)),cfs);

_<z>:=PolynomialRing(Rationals());

poly:=[];

for i in [1 .. #P] do;
b:=UnivariateEliminationIdealGenerators(P[i]);

for j in [1 .. #b] do;
addPoly,_:=UnivariatePolynomial(b[j]);
if Degree(addPoly) gt 1 then;
Include(~poly,addPoly); end if;
end for; end for;

NumbFlds:=[OptimisedRepresentation(NumberField(i)) : i in poly];

IsomClass:=[];
while #NumbFlds gt 0 do;
Append(~IsomClass,NumbFlds[1]);
ridOf:=[NumbFlds[1]];
for j in [2 .. #NumbFlds] do;
if IsIsomorphic(NumbFlds[1],NumbFlds[j]) eq true then;
Append(~ridOf,NumbFlds[j]);
end if;
end for;

for j in [1 .. #ridOf] do;
Exclude(~NumbFlds,ridOf[j]);
end for;

end while;

pols:=[DefiningPolynomial(i) : i in IsomClass];

//K:=SplittingField(pols);
time e1,e2,e3,e4 := SplitAutGrp(pols:Prime := NextPrime(10^6)); //Replace K with this//

//Next up I want the 240 points.
//Cheat way: 
X := Cluster(AffineSpace(Universe(a)),cfs);
time Y:=Points(X,e1);

e1t<tt>:=FunctionField(e1);
Et:=ChangeRing(E,e1t);

P:=[];
for i in [1 .. #Y] do
P[i]:=Et![Y[i][1]*tt^2+Y[i][2]*tt+Y[i][3],Y[i][4]*tt^3+Y[i][5]*tt^2+Y[i][6]*tt+Y[i][7],1];
end for;

function PrimeUse(poly);

test:=0;
while test eq 0 do;
p:=RandomPrime(20);
e1p:=GF(p);
_<x>:=PolynomialRing(e1p);

polyP:=[ChangeRing(i,e1p) : i in poly];


test:=1;
for i in [1 .. #polyP] do;
if #Roots(polyP[i]) ne Degree(polyP[i]) then;
test:=0;
end if;
end for;

ZK:= RingOfIntegers(e1);
Gpideal:=p*ZK;
primeID:=Factorization(Gpideal)[1][1];

if RamificationDegree(primeID,p) gt 1 then;
test:=0;
end if;

end while;
return p,primeID;
end function;

p,primeID:=PrimeUse(poly);


Gp:=GF(p);
Gz<z>:=PolynomialRing(Gp);
Gtp<tp>:=FunctionField(Gp);

gal:=Inverse(NumberingMap(e2));
ZK:= RingOfIntegers(e1);
FFpp, mpp :=ResidueClassField(primeID);
Fpt<tp>:=FunctionField(FFpp);
ZKt<tt> :=PolynomialRing(ZK);
Ep:=ChangeRing(E,Fpt);
bar := map<ZKt -> Fpt | f :-> Fpt![mpp(c) : c in Eltseq(f)]>;

Pp:=[];
for i in [1 .. #P] do;
Pp[i]:=Ep![FFpp!(1/Denominator(Coefficient(Numerator(P[i][1]),2)))*bar(Numerator(Coefficient(Numerator(P[i][1]),2)))*tp^2+FFpp!(1/Denominator(Coefficient(Numerator(P[i][1]),1)))*bar(Numerator(Coefficient(Numerator(P[i][1]),1)))*tp+FFpp!(1/Denominator(Coefficient(Numerator(P[i][1]),0)))*bar(Numerator(Coefficient(Numerator(P[i][1]),0))),FFpp!(1/Denominator(Coefficient(Numerator(P[i][2]),3)))*bar(Numerator(Coefficient(Numerator(P[i][2]),3)))*tp^3+FFpp!(1/Denominator(Coefficient(Numerator(P[i][2]),2)))*bar(Numerator(Coefficient(Numerator(P[i][2]),2)))*tp^2+FFpp!(1/Denominator(Coefficient(Numerator(P[i][2]),1)))*bar(Numerator(Coefficient(Numerator(P[i][2]),1)))*tp+FFpp!(1/Denominator(Coefficient(Numerator(P[i][2]),0)))*bar(Numerator(Coefficient(Numerator(P[i][2]),0))),1];
end for; 

Sp:=IndependentGenerators(Pp);
S:=[P[Index(Pp,Sp[i])] : i in [1 .. #Sp] ];

M:=[];
time for i in [1 .. #e2] do;
g:=[];
m:=[];
for j in [1 .. #S] do;
bb:=[(e3(gal(i))(Coefficient(Numerator(S[j][1]),2))),(e3(gal(i))(Coefficient(Numerator(S[j][1]),1))),(1*e3(gal(i))(Coefficient(Numerator(S[j][1]),0))),(e3(gal(i))(Coefficient(Numerator(S[j][2]),3))),(e3(gal(i))(Coefficient(Numerator(S[j][2]),2))),(e3(gal(i))(Coefficient(Numerator(S[j][2]),1))),(e3(gal(i))(Coefficient(Numerator(S[j][2]),0))*1)];

point:=Ep![FFpp!(1/Denominator(bb[1]))*bar(Numerator(bb[1]))*tp^2 + FFpp!(1/Denominator(bb[2]))*bar(Numerator(bb[2]))*tp + FFpp!(1/Denominator(bb[3]))*bar(Numerator(bb[3])),FFpp!(1/Denominator(bb[4]))*bar(Numerator(bb[4]))*tp^3 + FFpp!(1/Denominator(bb[5]))*bar(Numerator(bb[5]))*tp^2 + FFpp!(1/Denominator(bb[6]))*bar(Numerator(bb[6]))*tp + FFpp!(1/Denominator(bb[7]))*bar(Numerator(bb[7])),1];

_,g[j]:=IsLinearlyDependent(Append(Sp,point));
gg:=ElementToSequence(g[j]);
if gg[#gg] eq -1 then;
m[j]:=[gg[k]: k in [1 .. #Sp]]; end if;
if gg[#gg] eq 1 then;
m[j]:=[-gg[k]: k in [1 .. #Sp]]; end if;
end for;
M[i]:=Eltseq(Matrix(Rationals(),#S,#S,m));
end for;

GalG:=MatrixGroup<#S,Rationals()|M>;

can,iso:=IsIsomorphic(e2,GalG);

yum:=[M[Index(M,Eltseq(iso(e2.i)))] : i in [1 .. #Generators(e2)]];


A:=MatrixAlgebra<Rationals(),#S|yum>;
B:=RModule(A) ;
C:=GModule(e2,B);
D:=ConstituentsWithMultiplicities(C);
F:=[<Character(D[i][1]),D[i][2]> : i in [1 .. #D]];

return #S, e1, e2,S,F;

end function;

//Done!!


r,e1,e2,S,F:=RationalEllipticSurface(E);


/*
Examples:
Rank 2
E:=EllipticCurve([0,t^2*(t+1)]);

Rank 4
E:=EllipticCurve([0,t^4+t^2]);

Rank 6
E:=EllipticCurve([0,t*(t^3+1)]); 

Rank 8
E:=EllipticCurve([0,t^5+1]); */
