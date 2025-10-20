{\rtf1\ansi\ansicpg1252\cocoartf2865
\cocoatextscaling0\cocoaplatform0{\fonttbl\f0\fnil\fcharset0 Menlo-Regular;\f1\froman\fcharset0 Times-Roman;}
{\colortbl;\red255\green255\blue255;\red0\green0\blue0;\red0\green0\blue0;}
{\*\expandedcolortbl;;\csgray\c0;\cssrgb\c0\c0\c0;}
\paperw11900\paperh16840\margl1440\margr1440\vieww25820\viewh14100\viewkind0
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\f0\fs32 \cf2 \CocoaLigature0 /*When on Toby*/\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs30 Attach("/home/blair/+IdealsNF.m");\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 Attach("/home/blair/Subfields.m");\
Attach("/home/blair/Galois.m");\
Attach("/home/blair/GalAuto.m");\
Attach("/home/blair/Invar.m");\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
Attach("+IdealsNF.m");\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs34 Attach("AutSplit.m");
\fs32 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
_<t>:=FunctionField(Rationals());
\fs28 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 E:=EllipticCurve([0,t^4+t^2]);
\fs28 \
\
\
function RationalEllipticSurface(E);\
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
_<[a]> := PolynomialRing(Rationals(),7);\
_<tt> := PolynomialRing(Universe(a));\
x := a[1]*tt^2 + a[2]*tt + a[3];\
y := a[4]*tt^3 + a[5]*tt^2 + a[6]*tt + a[7];\

\fs32 ftmap:=hom<Parent(t) -> Parent(tt)| tt>;
\fs28 \

\fs32 coor:=[Parent(x)!ftmap(Coefficients(E))[i] : i in [1..5] ];
\fs28 \
cfs:= Coefficients(y^2 + coor[1]*x*y + coor[3]*y -x^3 - coor[2]*x^2-coor[4]*x-coor[5]);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs30 I:=ideal<Universe(a) | cfs>;\
_,P:=PrimaryDecomposition(I);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs28 //X := Cluster(AffineSpace(Universe(a)),cfs);
\fs30 \
\
_<z>:=PolynomialRing(Rationals());\
\
poly:=[];\
\
for i in [1 .. #P] do;\
b:=UnivariateEliminationIdealGenerators(P[i]);\
\
for j in [1 .. #b] do;\
addPoly,_:=UnivariatePolynomial(b[j]);\
if Degree(addPoly) gt 1 then;\
Include(~poly,addPoly); end if;\
end for; end for;\
\

\fs32 NumbFlds:=[OptimisedRepresentation(NumberField(i)) : i in poly];\
\
IsomClass:=[];\
while #NumbFlds gt 0 do;
\fs30 \
Append(~IsomClass,NumbFlds[1]);\
ridOf:=[NumbFlds[1]];\
for j in [2 .. #NumbFlds] do;\
if IsIsomorphic(NumbFlds[1],NumbFlds[j]) eq true then;\
Append(~ridOf,NumbFlds[j]);\
end if;\
end for;\
\
for j in [1 .. #ridOf] do;\
Exclude(~NumbFlds,ridOf[j]);\
end for;\
\
end while;\
\
pols:=[DefiningPolynomial(i) : i in IsomClass];\
\
//K:=SplittingField(pols);\
time e1,e2,e3,e4 := SplitAutGrp(poly:Prime := NextPrime(10^6)); //Replace K with this//\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
//Next up I want the 240 points.\
//Cheat way: \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs28 X := Cluster(AffineSpace(Universe(a)),cfs);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
time Y:=Points(X,e1);\
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 e1t<tt>:=FunctionField(e1);\
Et:=ChangeRing(E,e1t);
\fs28 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
P:=[];\
for i in [1 .. #Y] do\
P[i]:=Et![Y[i][1]*tt^2+Y[i][2]*tt+Y[i][3],Y[i][4]*tt^3+Y[i][5]*tt^2+Y[i][6]*tt+Y[i][7],1];\
end for;
\fs30 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
function PrimeUse(poly);\
\
test:=0;\
while test eq 0 do;\
p:=
\fs32 RandomPrime(20);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
Kp:=GF(p);
\fs30 \

\fs32 _<x>:=PolynomialRing(Kp);\
\
polyP:=[ChangeRing(i,Kp) : i in poly];\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs30 \
\
test:=1;\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
for i in [1 .. #polyP] do;\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 if #Roots(polyP[i]) ne Degree(polyP[i]) then;
\fs30 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
test:=0;\
end if;\
end for;\
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
Gpideal:=ideal(e1,p);\
Factorization(~Gpideal);\
primeID:=e1`PrimeIdeals[p,1];\
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs38 if e1`PrimeIdeals[p,1]`f gt 1 then;
\fs30 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
test:=0;\
end if;\
\
end while;\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
return p,primeID;\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
end function;\
\
p,primeID:=PrimeUse(poly);\
\
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs34 Gp:=GF(p);\
Gz<z>:=PolynomialRing(Gp);\
Gtp<tp>:=FunctionField(Gp);
\fs30 \
Ep:=ChangeRing(E,Gtp);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 gal:=Inverse(NumberingMap(e2));
\fs30 \
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
Pp:=[];\
for i in [1 .. #P] do;\
Pp[i]:=Ep![Gp!(Coefficient(Numerator(P[i][1]),2) mod primeID)
\fs28 *tp^2+
\fs30 Gp!(Coefficient(Numerator(P[i][1]),1) mod primeID)
\fs28 *tp+
\fs30 Gp!(Coefficient(Numerator(P[i][1]),0) mod primeID)
\fs28 ,
\fs30 Gp!(Coefficient(Numerator(P[i][2]),3) mod primeID)
\fs28 *tp^3+
\fs30 Gp!(Coefficient(Numerator(P[i][2]),2) mod primeID)
\fs28 *tp^2+
\fs30 Gp!(Coefficient(Numerator(P[i][2]),1) mod primeID)
\fs28 *tp+
\fs30 Gp!(Coefficient(Numerator(P[i][2]),0) mod primeID)
\fs28 ,1];\
end for; 
\fs30 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
Sp:=
\fs34 IndependentGenerators(Pp);\
S:=[P[Index(Pp,Sp[i])] : i in [1 .. #Sp] ];
\fs30 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs34 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 M:=[];\
time for i in [1 .. #e2] do;\
g:=[];\
m:=[];\
for j in [1 .. #S] do;\
point:=Ep![(
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][1]),2))
\fs30 mod primeID
\fs32 )*tp^2 + (
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][1]),1))
\fs30 mod primeID
\fs32 )*tp + (1*
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][1]),0))
\fs30 mod primeID
\fs32 ),(
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][2]),3))
\fs30 mod primeID
\fs32 )*tp^3 + (
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][2]),2))
\fs30 mod primeID
\fs32 )*tp^2 + (
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][2]),1))
\fs30 mod primeID
\fs32 )*tp + (
\fs30 e3(gal(i))
\fs32 (Coefficient(Numerator(S[j][2]),0))*1
\fs30 mod primeID
\fs32 )];\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs30 _,g[j]:=IsLinearlyDependent(Append(Sp,point));\
gg:=
\fs34 ElementToSequence
\fs30 (g[j]);\
if gg[#gg] eq -1 then;\
m[j]:=[gg[k]: k in [1 .. #Sp]]; end if;\
if gg[#gg] eq 1 then;\
m[j]:=[-gg[k]: k in [1 .. #Sp]]; end if;
\fs32 \
end for;\
M[i]:=Eltseq(Matrix(Rationals(),#S,#S,m));\
end for;
\fs34 \
\

\fs30 GalG:=MatrixGroup<#S,Rationals()|M>;
\fs34 \
\

\fs30 can,iso:=IsIsomorphic(e2,GalG);\
\
\
\
yum:=[M[Index(M,Eltseq(iso(e2.i)))] : i in [1 .. #Generators(e2)]];\
\
\
\
A:=MatrixAlgebra<Rationals(),#S|yum>;\
\pard\pardeftab720\sa240\partightenfactor0

\f1\fs32 \cf3 \expnd0\expndtw0\kerning0
\CocoaLigature1 B:=RModule(A) ;
\f0\fs30 \cf2 \kerning1\expnd0\expndtw0 \CocoaLigature0 \
C:=GModule(e2,B);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
D:=ConstituentsWithMultiplicities(C);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs36 F:=[<Character(D[i][1]),D[i][2]> : i in [1 .. #D]];\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs34 \
return #S, e1, e2,S,F;\
\
end function;\
\
//Done!!\
\
\
r,e1,e2,S,F:=
\fs28 RationalEllipticSurface(E);
\fs34 \
\
\
/*\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs32 Examples:\
Rank 2\
E:=EllipticCurve([0,t^2*(t+1)]);\
\
Rank 4\
E:=EllipticCurve([0,t^4+t^2]);\
\
Rank 6\
E:=EllipticCurve([0,t*(t^3+1)]); \
\
Rank 8\
E:=EllipticCurve([0,t^5+1]); */\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs34 \
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0

\fs30 I2L:=ChangeRing(P[1],K);\
La:=Generic(I2L);\
IL2p:=I2L + ideal<La | La.1-r>;\
X2:=GroebnerBasis(IL2p);\
\pard\tx560\tx1120\tx1680\tx2240\tx2800\tx3360\tx3920\tx4480\tx5040\tx5600\tx6160\tx6720\pardirnatural\partightenfactor0
\
}