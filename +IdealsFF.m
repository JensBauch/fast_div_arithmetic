//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//    +IdealsFunctionFields Package 
//    Jens-Dietrich Bauch 
//    April 2010
//    (C) 2013 Jens-Dietrich Bauch
//    Distributed under the terms of the GNU General Public License 
//    http://www.gnu.org/licenses/gpl.txt  
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
//    Many routines are translations from the package +Ideals.m
//	  The package is implemented for Magma V2.17-6	
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////


declare verbose montestalk, 4;
declare verbose hds, 4;
declare attributes FldFun: 
pBasis, Discriminant, FactorizedDiscriminant, FactorizedPrimes, IntegralBasis,
LocalIndex, pHermiteBasis, PrimeIdeals, TreesIntervals, localbasedata,maxorderfinite,
Times, SFLCount;
		
		
//Attributes for dealing with places at infinity

AddAttribute(FldFun,"PrimesAtInfinity");
AddAttribute(FldFun,"Cf");
AddAttribute(FldFun,"InfinityRepresentation");
AddAttribute(FldFun,"Fin");
AddAttribute(FldFun,"Genus");
AddAttribute(FldFun,"Index");
AddAttribute(FldFun,"IndexBases");
AddAttribute(FldFun,"MonicDefiningPoly");
AddAttribute(FldFun,"ReductionON");
AddAttribute(FldFun,"DivisorOfDegree1");
AddAttribute(FldFun,"ConstanFieldIndex");
//Records for places and Divisors

PlaceRecord:=recformat<
    FiniteIdeal: Rec, 
    InfiniteIdeal: Rec,
    FactorizationString:  MonStgElt,
    SuccessiveMinima:	SeqEnum,
    ApproximatedSuccessiveMinima:	SeqEnum,
	RedBasis:	SeqEnum,
	SRedBasis:	SeqEnum,
	Basis:	SeqEnum,
	SmallDiv:	Rec,
	r:	RngIntElt,
	a:	FldFunElt,	
	IsPrincipal:	BoolElt
    >;

//Records for montes algorithm
				
PrimeIdealRecord:=recformat<
Type: SeqEnum,
Parent: FldFun,
Pol: RngUPolElt,
PolynomialGenerator: RngUPolElt,
e: Integers(),
f: Integers(),
exponent: RngIntElt,
LocalGenerator: FldFunElt,
LogLG: ModTupRngElt,
Generator: FldFunElt,
CrossedValues: SeqEnum,
OkutsuBasis: SeqEnum,
Position: Integers()

>;


IdealRecord:=recformat<
Generators: SeqEnum , 
Norm: RngUPolElt,
Parent: FldFun,
Radical: SeqEnum,
IsIntegral: BoolElt,
IsPrime: BoolElt,
Factorization: List,
FactorizationString:  MonStgElt,
PolynomialGenerator: RngUPolElt,
Generator: FldFunElt,
Basis: SeqEnum,
PBasis: SeqEnum,            /* only for prime ideals */
PBasisVals: SeqEnum,        /* only for prime ideals */
Position: Integers(),       /* only for prime ideals */  
Type: SeqEnum,              /* only for prime ideals */
e: Integers(),              /* only for prime ideals */
f: Integers(),              /* only for prime ideals */
exponent: RngIntElt,       /* only for prime ideals */
LocalGenerator: FldFun,  /* only for prime ideals */
LogLG: ModTupRngElt,        /* only for prime ideals */
CrossedValues: SeqEnum      /* only for prime ideals */
>;


TypeLevel:=recformat<
Phi: RngUPolElt,
V: Integers(),
h: Integers(),
e: Integers(),
f: Integers(),
prode: Integers(),  /* e1*...*e(k-1) */
prodf: Integers(),  /* f1*...*f(k-1) */
invh: Integers(),
slope,
psi: RngUPolElt,
Fq: Fld,
FqY:RngUPol,
z: FldElt,
omega: Integers(),
cuttingslope: Integers(),
Refinements: List, 
alpha: Integers(),
logPi: ModTupRngElt,
logPhi: ModTupRngElt,
logGamma: ModTupRngElt,
PolynomialGenerator : RngUPolElt,     /* only in level 1 */   // should be Prime!!
Pol : RngUPolElt,       /* only in level 1 */
ProdQuots: SeqEnum,     /* only in level 1 */
ProdQuotsVals: SeqEnum, /* only in level 1 */
Phiadic: SeqEnum,       /* only in level 1 */
sfl: SeqEnum,            /* only in level 1 */
Redmap: Map,
map: Map
>;



OkutsuFrameLevel := recformat<
    degree: RngIntElt,
    index: RngIntElt,
    values: List,
    polynomial: RngUPolElt
>;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic InfinityRepresentation(F::FldFun)->FldFun
{Input: Function field F with indeterminate T, outpout: Function field F with indeterminate 1/T}

	F`Fin:=1;
	if not assigned F`InfinityRepresentation or not assigned F`Cf then
		kt:=PolynomialRing(ConstantField(F));	t:=kt.1;	T:=BaseField(F).1;
		f:=DefiningMonicPolynomial(F);	n:=Degree(f);	Coeff:=Coefficients(f);

		Cf:=Maximum([Ceiling(Degree(Coeff[j])/(-j+n+1)): j in [1..#Coeff-1]]);
		CoeffList:=Eltseq(T^(-n*Cf)*PolynomialRing(Parent(T))!Evaluate(f,t^Cf*Parent(f).1));
		CoeffNewf:=[];
		for i in CoeffList do
			TMP:=0;
			for j in Terms(Numerator(i)) do 
				TMP:=TMP+LeadingCoefficient(j)*t^(Degree(Denominator(i))-Degree(j));
			end for;
			Append(~CoeffNewf,TMP);
		end for;
		Newf:=Parent(f)!CoeffNewf;

		F`InfinityRepresentation:=FunctionField(Newf);
		F`Cf:=Cf;
	else
		return 	F`InfinityRepresentation;
		
	end if;
	F`InfinityRepresentation`Fin:=0;
	F`InfinityRepresentation`InfinityRepresentation:=F;
	F`InfinityRepresentation`Cf:=F`Cf;
	return F`InfinityRepresentation,F`Cf;

end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic TranslationMap(z::FldFunElt,F::FldFun)->FldFunElt
{Input: z element of function field F with indeterminate T, output: z element of 
isomorphic function field F` with indeterminate 1/T }

	K:=Parent(z); KT:=BaseField(K);	T:=KT.1;
	Coeffs:=Eltseq(z);
	d:=K`Cf;
	Newz:=F![Evaluate(Coeffs[i],1/T)*(1/T)^(d*(i-1)):i in [1..Degree(F)]];
	return Newz;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
/////////Divisor Arithmetic///////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Place(P::Rec)->Rec
{Construction of the place of a record}

require IsPrimeIdeal(P): "Argument should be a prime ideal";

	K:=P`Parent;

	if not assigned K`InfinityRepresentation then
		K`InfinityRepresentation:=InfinityRepresentation(K);
	end if;

	if not assigned K`Fin then
		K`InfinityRepresentation:=InfinityRepresentation(K);
		D:= rec<PlaceRecord|FiniteIdeal:=P,InfiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),FactorizationString:=SumListToString((P^1)`Factorization,false)>;
	else
		if K`Fin eq 1 then
			D:= rec<PlaceRecord|FiniteIdeal:=P,InfiniteIdeal:=ideal(K`InfinityRepresentation,
			K`InfinityRepresentation!1),FactorizationString:=SumListToString((P^1)`Factorization,false)>;	
		else	
			D:= rec<PlaceRecord|FiniteIdeal:=ideal(K`InfinityRepresentation,K`InfinityRepresentation!1),
			InfiniteIdeal:=P,FactorizationString:=Sprintf( "P(%o,%o)", 1/P`Parent!P`PolynomialGenerator,P`Position)  >;
		end if;
	end if;	
if IsReductionOn(K) then
			DivisorReduction(~D);
end if; 

return D;	

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Add(D1::Rec,D2::Rec)->Rec
{Adding two divisors in OM representation}

	Dfin:=D1`FiniteIdeal*D2`FiniteIdeal;
	Dinf:=D1`InfiniteIdeal*D2`InfiniteIdeal;

	temp1:=SumListToString((Dfin^-1)`Factorization,false);
	temp2:=SumListToString((Dinf^-1)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,
		FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,
		FactorizationString:=temp1 cat temp2>;
	end if;
		
	return D;	
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic '+'(D1::Rec,D2::Rec)->Rec
{Adding two divisors in OM representation}

F:=D1`FiniteIdeal`Parent;

if IsReductionOn(F) then
	D:=Add(D1,D2);
	DivisorReduction(~D1);	DivisorReduction(~D2);
	D1_tmp:=D1`SmallDiv;	D1_r:=D1`r;	 D1_a:=D1`a;
	D2_tmp:=D2`SmallDiv;	D2_r:=D2`r;	 D2_a:=D2`a;	
	Dtmp:=Add(D1_tmp,D2_tmp);
	DivisorReduction(~Dtmp);
	D`SmallDiv:=Dtmp`SmallDiv;	D`r:=D1_r+D2_r+Dtmp`r;	D`a:=D1_a*D2_a*Dtmp`a;
	return D;
	
end if;
	
return Add(D1,D2);

		
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '-'(D1::Rec,D2::Rec)->Rec
{Subtraction of two divisor in OM representation}

	Dfin:=D1`FiniteIdeal*(D2`FiniteIdeal)^-1;
	Dinf:=D1`InfiniteIdeal*(D2`InfiniteIdeal)^-1;

	temp1:=SumListToString((Dfin^-1)`Factorization,false);
	temp2:=SumListToString((Dinf^-1)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
	end if;
	return D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '*'(k::RngIntElt,D::Rec)->Rec
{Multiplying a divisor in OM representation with an integer}

	F:=D`FiniteIdeal`Parent;
	Dfin:=D`FiniteIdeal^k;
	Dinf:=D`InfiniteIdeal^k;
	D_old:=D;
	temp1:=SumListToString((Dfin^-1)`Factorization,false);
	temp2:=SumListToString((Dinf^-1)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
	end if;
	
	if IsReductionOn(F) then
	
		DivisorReduction(~D_old);
		SetReduction(F:On:=false);
		Dtmp:=k*D_old`SmallDiv;
		DivisorReduction(~Dtmp);
		D`SmallDiv:=Dtmp`SmallDiv;
		D`r:=Dtmp`r+k*D_old`r;
		D`a:=Dtmp`a*D_old`a^k;
		SetReduction(F);
	
	end if;
	
	return D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic Divisor(I::Rec)->Rec
{Input: A fractional ideal I in OM representation; 
Output: A divisor in OM representation having the ideal representation I and the trivial ideal.}

	K:=I`Parent;
	if not assigned K`Fin then
		K`Fin:=1;
	end if;
	if not assigned  K`InfinityRepresentation then
		K`InfinityRepresentation:=InfinityRepresentation(K);
	end if;
	if not assigned (I^1)`Factorization and K`Fin eq 1 then 

		D:= rec<PlaceRecord|FiniteIdeal:=ideal(K,K!1),
		InfiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),FactorizationString:="">;
	end if;
	if not assigned (I^1)`Factorization and K`Fin eq 0 then 

		D:= rec<PlaceRecord|FiniteIdeal:=ideal(K`InfinityRepresentation
		,K`InfinityRepresentation!1),
		InfiniteIdeal:=ideal(K,K!1),FactorizationString:="">;
	end if;
	if K`Fin eq 1 then 

		D:= rec<PlaceRecord|FiniteIdeal:=I,InfiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),
		FactorizationString:=SumListToString((I^-1)`Factorization,false)>;
	else	

		D:= rec<PlaceRecord|FiniteIdeal:=ideal(K`InfinityRepresentation,
		K`InfinityRepresentation!1),InfiniteIdeal:=I,
		FactorizationString:=SumListToString((I^-1)`Factorization,true)>;
	end if;

	if IsReductionOn(K) then
			DivisorReduction(~D);
	end if;	
	
	return D;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Divisor(z::FldFunElt)->Rec
{Produces the principal divisor in OM representation of non-zero function of a function field}

	require not z eq 0: "Argument should be a non zero";
	K:=Parent(z);
				
	Ifin:=ideal(K,z)^1;

	Iinf:=&*[i^(PValuation(z,i)): i in PrimesAtInfinity(K)];

	temp1:=SumListToString((Ifin)`Factorization,false);
	temp2:=SumListToString((Iinf)`Factorization,true);

	if #temp1 gt 0 and #temp2 gt 0 then
		D:=rec<PlaceRecord|FiniteIdeal:=Ifin^-1,InfiniteIdeal:=Iinf^-1,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
	else
		D:=rec<PlaceRecord|FiniteIdeal:=Ifin^-1,InfiniteIdeal:=Iinf^-1,FactorizationString:=temp1 cat temp2>;
	end if;
	D`IsPrincipal:=true;	

	D`a:=1/z;
	if IsReductionOn(K) then
			D`SmallDiv:=Divisor(K!1);	D`r:=0;			
	end if;	

	return D;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Support(D::Rec)->SeqEnum
{Determines the support of a divisor}

	K:=D`FiniteIdeal`Parent;
	L1:=((D`FiniteIdeal)^-1)`Factorization;
	FinitePrimes:=[];	FiniteExponents:=[];
	for i in L1 do
		Append(~FinitePrimes,K`PrimeIdeals[i[1],i[2]]);
		Append(~FiniteExponents,i[3]);
	end for;

	L2:=((D`InfiniteIdeal)^-1)`Factorization;	PAI:=PrimesAtInfinity(K);
	InfinitePrimes:=[];	InfiniteExponents:=[];
	for i in L2 do
		Append(~InfinitePrimes,PAI[i[2]]);
		Append(~InfiniteExponents,i[3]);
	end for;
	
	return InfinitePrimes cat FinitePrimes,InfiniteExponents cat FiniteExponents;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic GCD(D1::Rec,D2::Rec)->Rec
{Determines the GCD of D1 and D2}

GC:=[]; Expo_1:=[];	Expo_2:=[];
PL_1,Ex_1:=Support(D1);	PL_2,Ex_2:=Support(D2);
for i in [1..#PL_1] do
	for j in [1..#PL_2] do
		if PL_1[i] eq PL_2[j] then 
			Append(~GC,PL_1[i]);
			Append(~Expo_1,Ex_1[i]);
			Append(~Expo_2,Ex_2[j]);
		end if;
	end for;	
end for;
return GC,Expo_1,Expo_2;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Height(D::Rec)->RngIntElt
{Determines the height of a divisor}

	Supp,Expos:=Support(D);
	if #Expos eq 0 then
		return 0,0;
	else
		return &+[Abs(Expos[i])*Degree(Supp[i]):i in [1..#Expos]],Maximum([Degree(Supp[i]):i in [1..#Expos]]);
	end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PlacesAtInfinity(K::FldFun)->SeqEnum
{Produces the places at infinity of K}

	if not assigned K`PrimesAtInfinity then
	
		if not assigned K`InfinityRepresentation then
			K`InfinityRepresentation,K`Cf:=InfinityRepresentation(K);	
		end if;
	
		Montes(K`InfinityRepresentation,PolynomialRing(ConstantField(K)).1);
		K`PrimesAtInfinity:=K`InfinityRepresentation`PrimeIdeals[PolynomialRing(ConstantField(K)).1];
	
	end if;

	return [Place(i): i in K`PrimesAtInfinity];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PrimesAtInfinity(K::FldFun)->SeqEnum
{Produces the prime ideals of the infinite maximal order of K}

	if not assigned K`PrimesAtInfinity then
	
		if not assigned K`InfinityRepresentation then
			K`InfinityRepresentation,K`Cf:=InfinityRepresentation(K);	
		end if;
	
		Montes(K`InfinityRepresentation,PolynomialRing(ConstantField(K)).1);
		K`PrimesAtInfinity:=K`InfinityRepresentation`PrimeIdeals[PolynomialRing(ConstantField(K)).1];
	
	end if;

	return K`PrimesAtInfinity;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
/*
intrinsic Montes(K::FldFun,p::RngUPolElt: Basis:=false)
{}
require IsPrime(p): "First argument must be a prime polynomial";
Rt:=Parent(p);
Rxt<x>:=PolynomialRing(Rt);
RXT<T>:=BaseField(K);
Pol:=Rxt!DefiningMonicPolynomial(K);
//require (CoefficientRing(Pol) eq Integers() and IsMonic(Pol)): "Function Field must be defined by a monic integral polynomial";
if assigned K`PrimeIdeals then
	if IsDefined(K`PrimeIdeals,p) then
		return;
	end if;
end if;

if not assigned K`localbasedata then
    K`localbasedata:=AssociativeArray();
    K`IndexBases:=AssociativeArray();
    //K`maxorderfinite:=AssociativeArray();
end if;   
if not assigned K`FactorizedPrimes then
    K`FactorizedPrimes:=[];
    K`PrimeIdeals:=AssociativeArray();
    K`LocalIndex:=AssociativeArray();
    K`TreesIntervals:=AssociativeArray();
    K`pBasis:=AssociativeArray();
    K`pHermiteBasis:=AssociativeArray();
end if;    

Fp,map:=ResidueClassField(p);
Fpy<y>:=PolynomialRing(Fp:Global := false);
fa:=Factorization(Fpy![map(i): i in Coefficients(Pol)]);
totalindex:=0;   
OMReprs:=[];
TreesIntervals:=[];
right:=0;
BasisNums:=[];
BasisDens:=[];
for factor in fa do
    vprint montestalk,2: "Analyzing irreducible factor modulo p: ",factor[1];
    level:=InitialLevel(map,p,Pol,factor[1],factor[2]: BAS:=Basis);
    Leaves:=[];
    Montesloop(level,~Leaves,~totalindex,~BasisNums,~BasisDens: Basisloop:=Basis);
    Append(~TreesIntervals,[right+1..right+#Leaves]);  
    right+:=#Leaves;
    OMReprs cat:=Leaves;  
end for;
if #OMReprs eq 1 then
    OMReprs[1,#OMReprs[1]]`Phi:=Pol;
    OMReprs[1,#OMReprs[1]]`slope:=Infinity();
end if;
K`PrimeIdeals[p]:=[];
Psi:=0;
logLG:=0;
primeid:=rec<PrimeIdealRecord|Parent:=K,Pol:=Pol,PolynomialGenerator:=p>;
for k:=1 to #OMReprs do
    primeid`Position:=k;
    primeid`Type:=OMReprs[k];
    primeid`e:=OMReprs[k][#OMReprs[k]]`prode;
    primeid`f:=OMReprs[k][#OMReprs[k]]`prodf; 
    PrescribedValue(~OMReprs[k],1,~Psi,~logLG);
    primeid`LocalGenerator:=Evaluate(K,Psi)*RXT!p^logLG[1];
    primeid`LogLG:=logLG;
    primeid`exponent:=OMReprs[k,1]`sfl[1];
    Append(~K`PrimeIdeals[p],primeid); 
end for;
Append(~K`FactorizedPrimes,p);
Sort(~K`FactorizedPrimes);
K`LocalIndex[p]:=totalindex;
K`TreesIntervals[p]:=TreesIntervals;
CrossedValues(~K,p);
if Basis then
	// war vorher drauÃŸen aus der if-schleife
    K`pBasis[p]:=[Evaluate(BasisNums[k],K.1)/p^Floor(BasisDens[k]): k in [1..Degree(K)]];
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Montesloop(level,~Leaves,~totalindex,~BasisNums,~BasisDens: Basisloop:=false)
{}
	
Stack:=[[level]];
while #Stack gt 0 do	  
    type:=Stack[#Stack];
    Prune(~Stack);
    r:=#type;
vprint montestalk,2:  "Analyzing type of order ",r;
vprint montestalk,2:  "Phir=",type[r]`Phi;
    Phiadic,Quotients:=Taylor(type[1]`Pol,type[r]`Phi,type[r]`omega);
    sides:=[];
    devsEachSide:=[* *];
    Newton(r,~type,~Phiadic,~sides,~devsEachSide);
    vprint montestalk,3: "Sides of Newton polygon:",sides;
    lengthN:=type[r]`omega;
    indexN:=-type[r]`cuttingslope*(lengthN*(lengthN-1) div 2); 
 
 
 
    if lengthN eq 1 then
	vprint montestalk,2:  "Found a factor of depth  ",r-1;
	//print"laste leven daten",Phiadic,sides[1],devsEachSide[1];
	LastLevel(Phiadic,~type,sides[1],devsEachSide[1]);
	Append(~Leaves,type);  
	sides:=[];
	if Basisloop and r eq 1 and type[1]`cuttingslope eq 0 then
	    BasisNums cat:=[Quotients[1]*x: x in type[1]`ProdQuots];
	    BasisDens cat:=type[1]`ProdQuotsVals;
	end if;
    end if;
    
    prevh:=0;	
    for i:=#sides to 1 by -1 do  // GRAN FOR SIDES
	side:=sides[i];
	vprint montestalk,2:  "Analyzing side ",side;      
	type[r]`h:=-Numerator(side[1]);
	type[r]`e:=Denominator(side[1]);
	type[r]`slope:=-side[1];
	type[r]`invh:=InverseMod(type[r]`h,type[r]`e);
	lprime:=(1-type[r]`invh*type[r]`h) div type[r]`e;
	newPi:=Eltseq(type[r]`invh*type[r]`logPhi+lprime*type[r]`logPi);
	Append(~newPi,0);  
	type[r]`logGamma:=type[r]`e*type[r]`logPhi-type[r]`h*type[r]`logPi;
   	Ei:=Integers()!(side[4]-side[2]);
	Hi:=Integers()!(side[3]-side[5]);
	indexN+:=Ei*prevh+((Ei*Hi-Ei-Hi+(Ei div type[r]`e))div 2);

	prevh+:=Hi;
	respol:=0;
	ResidualPolynomial(r,~type,~devsEachSide[i],~respol);
        respol:=respol/LeadingCoefficient(respol);
	factors:=Factorization(respol);
//if terminal side we add a piece of basis
	if Basisloop then
	    lengthPQ:=#type[1]`ProdQuots;
	    terminals:=[Degree(x[1]): x in factors|x[2] eq 1];
	    nonterminals:=[Degree(x[1]): x in factors|x[2] ne 1];
	    efS:=0;
	    efrest:=0;
	    if #terminals gt 0 then 
		efS:=type[r]`e*&+terminals; 
	    end if;
	    if #nonterminals gt 0 then 
		efrest:=type[r]`e*Max(nonterminals); 
	    end if;
	    efmax:=Max([efS,efrest]);
	    step:=(type[r]`slope+type[r]`V)/type[r]`prode;
	    height:=(side[5]-side[4]*type[r]`V)/type[r]`prode;
	    lastabscissa:=Integers()!side[4];
	    EnlargePQ:=[];
	    EnlargePQVals:=[];
	    for abscissa:=lastabscissa to lastabscissa-efmax+1 by -1 do
		EnlargePQ cat:=[Quotients[abscissa]*x mod type[1]`Pol: x in type[1]`ProdQuots];
		EnlargePQVals cat:=[height+x: x in type[1]`ProdQuotsVals];
		height:=height+step;
	    end for;
	    if efS gt 0 and Basisloop then// hier war kein basisloop in der if-abfrage
		BasisNums cat:=EnlargePQ[1..lengthPQ*efS];
		BasisDens cat:=EnlargePQVals[1..lengthPQ*efS];              
		vprint montestalk,3: "Terminal side. Basis updated to ",BasisNums," with valuations ",BasisDens;                      
	    end if;
	end if;
	vprint montestalk,2: "Monic Residual Polynomial=",respol;
        vprint montestalk,3:  "Factors of R.P.:=",factors;            
// PETIT FOR FACTORS	
        for factor in factors do       
	    vprint montestalk,2: "Analyzing factor of the Res.Pol.",factor[1];
            ta:=type;  
            ta[r]`psi:=factor[1];
	    ta[r]`f:=Degree(ta[r]`psi);
	    Representative(~ta);
// IF REFINA-AVANÃ‡A
	    if Degree(ta[r]`Phi) eq Degree(ta[r+1]`Phi) then
//	    print"refining";
		vprint montestalk,2:  "Refining. Cuttingslope=",-side[1];
		if #sides gt 1 or #factors gt 1 then
//			print"refining";
		    Append(~ta[r]`Refinements,[* ta[r]`Phi,ta[r]`slope *]);
		end if;
		ta[r]`cuttingslope:=-Integers()!side[1];
//		print"bloody side ",-Integers()!side[1];
		ta[r]`Phi:=ta[r+1]`Phi;
		ta[r]`omega:=factor[2];
		Prune(~ta);  
	    else
		vprint montestalk,2:  "Proceeding to higher order";    
		ta[r+1]`omega:=factor[2];
		ta[r+1]`logPi:=Vector(newPi);
		vec:=-ta[r+1]`V *ta[r+1]`logPi;
		vec[r+2]:=1;
		ta[r+1]`logPhi:=Vector(vec); 
		if Basisloop and factor[2] gt 1 then
		    lef:=lengthPQ*ta[r]`e*ta[r]`f;
		    ta[1]`ProdQuots cat:=EnlargePQ[lengthPQ+1..lef];	
		    ta[1]`ProdQuotsVals cat:=EnlargePQVals[lengthPQ+1..lef];
		end if;
            end if; 
// FINAL IF REFINA-AVANÃ‡A
	    Append(~Stack,ta);
        end for;     // FINAL PETIT FOR FACTORS
    end for;         // FINAL GRAN FOR SIDES
    totalindex+:=type[r]`prodf*indexN;
    vprint montestalk, 2: "Added  ",type[r]`prodf*indexN," to the index";
end while;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////


*/



intrinsic Montes(K::FldFun,p::RngUPolElt: Basis:=false)
{}
require IsPrime(p): "First argument must be a prime polynomial";
Rt:=Parent(p);
Rxt<x>:=PolynomialRing(Rt);
RXT<T>:=BaseField(K);
Pol:=Rxt!DefiningPolynomial(K);
//require (CoefficientRing(Pol) eq Integers() and IsMonic(Pol)): "Number Field must be defined by a monic integral polynomial";

if not assigned K`localbasedata then
    K`localbasedata:=AssociativeArray();
    K`IndexBases:=AssociativeArray();
    //K`maxorderfinite:=AssociativeArray();
end if;   
if not assigned K`FactorizedPrimes then
    K`FactorizedPrimes:=[];
    K`PrimeIdeals:=AssociativeArray();
    K`LocalIndex:=AssociativeArray();
    K`TreesIntervals:=AssociativeArray();
    K`pBasis:=AssociativeArray();
    K`pHermiteBasis:=AssociativeArray();
end if;    
if p in K`FactorizedPrimes and (not Basis or IsDefined(K`pBasis,p)) then
    return;
end if;

Fp,map:=ResidueClassField(p);
Fpy<y>:=PolynomialRing(Fp:Global := false);

fa:=Factorization(Fpy![map(i): i in Coefficients(Pol)]);

totalindex:=0;   
OMReprs:=[];
TreesIntervals:=[];
right:=0;
BasisNums:=[];
BasisDens:=[];

for factor in fa do
    vprint montestalk,2: "Analyzing irreducible factor modulo p: ",factor[1];

    level:=InitialLevel(map,p,Pol,factor[1],factor[2]: BAS:=Basis);
    Leaves:=[];
    Montesloop(level,~Leaves,~totalindex,~BasisNums,~BasisDens: Basisloop:=Basis);

    Append(~TreesIntervals,[right+1..right+#Leaves]);  
    right+:=#Leaves;

    OMReprs cat:=Leaves;  
end for;
if #OMReprs eq 1 then
    OMReprs[1,#OMReprs[1]]`Phi:=Pol;
    OMReprs[1,#OMReprs[1]]`slope:=Infinity();
end if;
K`PrimeIdeals[p]:=[];
Psi:=0;
logLG:=0;
primeid:=rec<PrimeIdealRecord|Parent:=K,Pol:=Pol,PolynomialGenerator:=p>;

for k:=1 to #OMReprs do
    primeid`Position:=k;
    primeid`Type:=OMReprs[k];
    primeid`e:=OMReprs[k][#OMReprs[k]]`prode;
    primeid`f:=OMReprs[k][#OMReprs[k]]`prodf; 
    PrescribedValue(~OMReprs[k],1,~Psi,~logLG);
    primeid`LocalGenerator:=Evaluate(K,Psi)*RXT!p^logLG[1];
    primeid`LogLG:=logLG;
    primeid`exponent:=OMReprs[k,1]`sfl[1];
    Append(~K`PrimeIdeals[p],primeid); 
end for;
Append(~K`FactorizedPrimes,p);
Sort(~K`FactorizedPrimes);

K`LocalIndex[p]:=totalindex;
K`TreesIntervals[p]:=TreesIntervals;
CrossedValues(~K,p);
if Basis then
	// war vorher drauÃŸen aus der if-schleife
    K`pBasis[p]:=[Evaluate(BasisNums[k],K.1)/p^Floor(BasisDens[k]): k in [1..Degree(K)]];
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Montesloop(level,~Leaves,~totalindex,~BasisNums,~BasisDens: Basisloop:=false)
{}
	
Stack:=[[level]];
while #Stack gt 0 do	  
    type:=Stack[#Stack];
    Prune(~Stack);
    r:=#type;

vprint montestalk,2:  "Analyzing type of order ",r;
vprint montestalk,2:  "Phir=",type[r]`Phi;
//print"before Talor";tt:=Realtime();
    Phiadic,Quotients:=Taylor(type[1]`Pol,type[r]`Phi,type[r]`omega);
//print"after Talor";Realtime()-tt;
    sides:=[];
    devsEachSide:=[* *];  
  //  print"before Newton"; tt:=Realtime();

    Newton(r,~type,~Phiadic,~sides,~devsEachSide);

    //print"after Newton";Realtime()-tt;
    vprint montestalk,3: "Sides of Newton polygon:",sides;
    lengthN:=type[r]`omega;
    indexN:=-type[r]`cuttingslope*(lengthN*(lengthN-1) div 2); 
    if lengthN eq 1 then
	vprint montestalk,2:  "Found a factor of depth  ",r-1;
//    print"before LastLevel";tt:=Realtime();

	LastLevel(Phiadic,~type,sides[1],devsEachSide[1]);

  //  print"after LastLevel";Realtime()-tt;
	Append(~Leaves,type);  
	sides:=[];
	if Basisloop and r eq 1 and type[1]`cuttingslope eq 0 then
	    BasisNums cat:=[Quotients[1]*x: x in type[1]`ProdQuots];
	    BasisDens cat:=type[1]`ProdQuotsVals;
	end if;
    end if;

    prevh:=0;	
    for i:=#sides to 1 by -1 do  // GRAN FOR SIDES
	side:=sides[i];
	vprint montestalk,2:  "Analyzing side ",side;     
	//print"sadasd 1";   
	type[r]`h:=-Numerator(side[1]);
	type[r]`e:=Denominator(side[1]);
	type[r]`slope:=-side[1];
	type[r]`invh:=InverseMod(type[r]`h,type[r]`e);
	lprime:=(1-type[r]`invh*type[r]`h) div type[r]`e;
	newPi:=Eltseq(type[r]`invh*type[r]`logPhi+lprime*type[r]`logPi);
	Append(~newPi,0);  
	type[r]`logGamma:=type[r]`e*type[r]`logPhi-type[r]`h*type[r]`logPi;
   	Ei:=Integers()!(side[4]-side[2]);
	Hi:=Integers()!(side[3]-side[5]);
	indexN+:=Ei*prevh+((Ei*Hi-Ei-Hi+(Ei div type[r]`e))div 2);

	prevh+:=Hi;
	respol:=0;    
   // print"before ResidualPolynomial";
	ResidualPolynomial(r,~type,~devsEachSide[i],~respol);
   // print"after ResidualPolynomial";Realtime()-tt;
        respol:=respol/LeadingCoefficient(respol);
	factors:=Factorization(respol);
//if terminal side we add a piece of basis
	if Basisloop then
	    lengthPQ:=#type[1]`ProdQuots;
	    terminals:=[Degree(x[1]): x in factors|x[2] eq 1];
	    nonterminals:=[Degree(x[1]): x in factors|x[2] ne 1];
	    efS:=0;
	    efrest:=0;
	    if #terminals gt 0 then 
		efS:=type[r]`e*&+terminals; 
	    end if;
	    if #nonterminals gt 0 then 
		efrest:=type[r]`e*Max(nonterminals); 
	    end if;
	    efmax:=Max([efS,efrest]);
	    step:=(type[r]`slope+type[r]`V)/type[r]`prode;

	    height:=(side[5]-side[4]*type[r]`V)/type[r]`prode;
	    lastabscissa:=Integers()!side[4];
	    EnlargePQ:=[];
	    EnlargePQVals:=[];
	    for abscissa:=lastabscissa to lastabscissa-efmax+1 by -1 do
		EnlargePQ cat:=[Quotients[abscissa]*x mod type[1]`Pol: x in type[1]`ProdQuots];
		EnlargePQVals cat:=[height+x: x in type[1]`ProdQuotsVals];
		height:=height+step;
	    end for;
	    if efS gt 0 and Basisloop then// hier war kein basisloop in der if-abfrage
		BasisNums cat:=EnlargePQ[1..lengthPQ*efS];
		BasisDens cat:=EnlargePQVals[1..lengthPQ*efS];              
		vprint montestalk,3: "Terminal side. Basis updated to ",BasisNums," with valuations ",BasisDens;                      
	    end if;
	end if;
	vprint montestalk,2: "Monic Residual Polynomial=",respol;
        vprint montestalk,3:  "Factors of R.P.:=",factors;            
// PETIT FOR FACTORS	
        for factor in factors do       
	    vprint montestalk,2: "Analyzing factor of the Res.Pol.",factor[1];
            ta:=type;  
            ta[r]`psi:=factor[1];
	    ta[r]`f:=Degree(ta[r]`psi);
	    Representative(~ta);
// IF REFINA-AVANÃ‡A

	    if Degree(ta[r]`Phi) eq Degree(ta[r+1]`Phi) then
		vprint montestalk,2:  "Refining. Cuttingslope=",-side[1];
		if #sides gt 1 or #factors gt 1 then
		    Append(~ta[r]`Refinements,[* ta[r]`Phi,ta[r]`slope *]);
		end if;
		ta[r]`cuttingslope:=-Integers()!side[1];
		ta[r]`Phi:=ta[r+1]`Phi;
		ta[r]`omega:=factor[2];
		Prune(~ta);  
	    else
		vprint montestalk,2:  "Proceeding to higher order";    
		ta[r+1]`omega:=factor[2];
		ta[r+1]`logPi:=Vector(newPi);
		vec:=-ta[r+1]`V *ta[r+1]`logPi;
		vec[r+2]:=1;
		ta[r+1]`logPhi:=Vector(vec); 
		if Basisloop and factor[2] gt 1 then
		    lef:=lengthPQ*ta[r]`e*ta[r]`f;
		    ta[1]`ProdQuots cat:=EnlargePQ[lengthPQ+1..lef];	
		    ta[1]`ProdQuotsVals cat:=EnlargePQVals[lengthPQ+1..lef];
		end if;
            end if; 
// FINAL IF REFINA-AVANÃ‡A
	    Append(~Stack,ta);
        end for;     // FINAL PETIT FOR FACTORS
    end for;         // FINAL GRAN FOR SIDES
    totalindex+:=type[r]`prodf*indexN;
    vprint montestalk, 2: "Added  ",type[r]`prodf*indexN," to the index";
end while;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////




intrinsic IsPrimeIdeal(I::Rec)->BoolElt
{True iff I is a record of type IdealRecord or PrimeIdealRecord corresponding to a prime ideal. }
require IsPrimeIdealRecord(I)  or IsIdealRecord(I) or IsPlace(I): "Argument should be an ideal record or a prime ideal record"; 

if IsPlace(I) then return false; end if;
if IsPrimeIdealRecord(I) then 
    return true;
else
    Factorization(~I);  
    return I`IsPrime ;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IsIdealRecord(I::Rec)->BoolElt
{True iff I is a record of type IdealRecord.}
return    Names(I) eq Names(rec<IdealRecord|>);
end intrinsic;

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IsPrimeIdealRecord(I::Rec)->BoolElt
{True iff I is a record of type PrimeIdealRecord.}
return    Names(I) eq Names(rec<PrimeIdealRecord|>);
end intrinsic;

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IsDivisor(D::Rec)->BoolElt
{True iff D is a record of type PlaceRecord.}
return    Names(D) eq Names(rec<PlaceRecord|>);
end intrinsic;

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IsPlace(P::Rec)->BoolElt
{True iff P is a record of type PlaceRecord.}
if    Names(P) eq Names(rec<PlaceRecord|>) then
	Ifin:=P`FiniteIdeal^1; 
	Iinf:=P`InfiniteIdeal^1;
	Factorization(~Ifin);	Factorization(~Iinf);
	if (#Ifin`Factorization eq 1 and #Iinf`Factorization eq 0 and Ifin`Factorization[1,3] eq 1)
		or (#Ifin`Factorization eq 0 and #Iinf`Factorization eq 1 and Iinf`Factorization[1,3] eq 1)
	then return true;
	end if;
end if;

return false;
end intrinsic;


//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic IsEffective(D::Rec)->BoolElt
{}
_,coeffs:=Support(D);
return    forall{i:i in coeffs|i  ge 0 };
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ideal(K::FldFun, listgen::SeqEnum[FldFunElt] )->Rec
{Define the fractional ideal generated by the elements of listgen.}
require &and[x in K: x in listgen]: "Elements should lie in the given function field.";
return rec<IdealRecord|  Generators:=listgen, Parent:=K>;
end intrinsic;

intrinsic ideal(K::FldFun, a:: FldFunElt )->Rec
{Define the principal fractional ideal generated by a}
require a in K: "Segon argument should lie in the given function field.";
return rec<IdealRecord|  Generators:=[a], Parent:=K>;
end intrinsic;

intrinsic ideal(K::FldFun, a:: RngUPolElt )->Rec
{Define the principal fractional ideal generated by the integer a}
return rec<IdealRecord|  Generators:=[K!a], Parent:=K>;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic SumListToString(list,inf)->MonStgElt
{Technical function to write down a factorization in a pretty form. For internal use only}
if #list eq 0 then return ""; end if;
R<t>:=Parent(list[1,1]);
str:="";
run:=0;
for x in list do
	run:=run+1;	
  if x[3] ne 1 then str:= str cat Sprintf(" %o*",x[3]) ; end if;
 	 if run eq #list then
 		if 	inf eq false then 
		  str:=str cat Sprintf( "P(%o,%o)", R!x[1],x[2]);
		else
	      str:=str cat Sprintf( "P(1/t,%o)", x[2]);  
	    end if;  
	else
		if 	inf eq false then 
			str:=str cat Sprintf( "P(%o,%o)+", R!x[1],x[2]);
		else
			str:=str cat Sprintf( "P(1/t,%o)+",x[2]);
		end if;	  
      end if;
end for;
return Substring(str,1,#str);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PValuation(alpha::FldFunElt, P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of alpha at the prime ideal P, which can be given either as PrimeIdealRecord or as an IdealRecord}

require IsPrimeIdeal(P) or IsPlace(P): "Second argument should be a prime ideal or a place";

if IsPlace(P) then
	
	tmp:=P`FiniteIdeal^1;
	if #(tmp`Factorization) eq 0 then
		P:=P`InfiniteIdeal;
	else
		P:=P`FiniteIdeal;
	end if;

end if;

F:=P`Parent;
if not alpha in F then
	f:=DefiningMonicPolynomial(F);
	n:=Degree(f);
	Coeff:=Coefficients(f);
	dtemp:=Maximum([Degree(Coeff[i])+(i-1): i in [1..#Coeff]]);
	d:=Ceiling(dtemp/n);
    return PValuation( TranslationMap(alpha,F),P);
else
	return PValuation(P`Parent!alpha,P);
end if;
end intrinsic;

intrinsic PValuation(alpha::RngUPolElt, P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of alpha at the prime ideal P, which can be given either as PrimeIdealRecord or as an IdealRecord}
return PValuation(P`Parent!alpha,P);
end intrinsic;

intrinsic PValuation(alpha::FldFunElt,P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of alpha at the prime ideal P, which can be given either as PrimeIdealRecord or as an IdealRecord.
Also the class of alpha in P^value/P^value+1}

require IsPrimeIdeal(P) or IsPlace(P): "Second argument should be a prime ideal or a place";

if IsPlace(P) then
	
	tmp:=P`FiniteIdeal^1;
	if #(tmp`Factorization) eq 0 then
		P:=P`InfiniteIdeal;
	else
		P:=P`FiniteIdeal;
	end if;

end if;

K:=P`Parent;
if not Parent(alpha) eq K then
	if not assigned K`Cf then
	f:=DefiningMonicPolynomial(K);
	n:=Degree(f);
	Coeff:=Coefficients(f);
	dtemp:=Maximum([Degree(Coeff[i])+(i-1): i in [1..#Coeff]]);
	d:=Ceiling(dtemp/n);
	else
	d:=K`Cf;
	end if;
    alpha:= TranslationMap(alpha,K);
end if;
require alpha in P`Parent: "Arguments should lie on the same function field";
r:=#P`Type;
p:=P`PolynomialGenerator;
Fp:=P`Type[1]`Fq;
Fpy:=P`Type[1]`FqY;
map:=P`Type[1]`Redmap;
reduction:=Fp!0;
if alpha eq 0 then 
    return Infinity(),reduction; 
end if;
den,exp,numPol:=Localize(alpha,P`PolynomialGenerator);
cua:=exp*P`e;

pphi:=[map(i):i in Eltseq(P`Type[1]`Phi)];
pnumPol:=[map(i):i in Eltseq(numPol)];

if VValuation(Fpy!pnumPol,Fpy!pphi) eq 0 then 
	if RED then
	ConvertLogs(~P`Type,-cua*P`LogLG,~reduction);
	reduction*:=(map(den))^(-1)*Evaluate(Fpy!pnumPol,P`Type[1]`z);
    end if;
    return cua,reduction; 
end if;

respol:=0;
z:=0;
dev:=[* *];
val:=0;
value:=0;
i:=0;
while value eq 0 do
 	if i lt #P`Type then
		i+:=1;
    else
		SFL(~P`Parent,~P,2*P`Type[#P`Type]`h);
    end if;
    Value(i+1,~P`Type,numPol,~dev,~val);
    ResidualPolynomial(i,~P`Type,~dev,~respol);
    if VValuation(respol,P`Type[i]`psi) eq 0 then
		value:=val*(P`e div (P`Type[i]`e*P`Type[i]`prode));
    end if;

end while;
if RED then
    log:=dev[#dev,1]*P`Type[i]`logPhi+dev[#dev,2]*P`Type[i]`logPi;
    EqualizeLogs(~P`LogLG,~log);
    ConvertLogs(~P`Type,log-(value+cua)*P`LogLG,~reduction);
    Z(~P`Type,i,~z);
    reduction*:=(Fp!den)^(-1)*Evaluate(respol,z);
end if;
return value+cua,reduction;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic PValuation(D::Rec, P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of a divisor at the prime ideal P}

require IsDivisor(D): "First argument should be a divisor";
require IsPrimeIdeal(P) or IsPlace(P): "Second argument should be a prime ideal or a place";

if IsPlace(P) then
	
	tmp:=P`FiniteIdeal^1;
	if #(tmp`Factorization) eq 0 then
		P:=P`InfiniteIdeal;
	else
		P:=P`FiniteIdeal;
	end if;

end if;
S1,S2:=Support(D);
bool,pos:=P in S1;
if bool then 
	return S2[pos];
else
	return 0;
end if;	
		

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic InitialLevel(map,p,Pol,psi,power: BAS:=false)-> Rec
{psi is a monic irreducible factor of Pol modulo p and power=ord_psi(Pol mod p)}

Kt<t>:=Parent(p);
Ktx<x>:=PolynomialRing(Kt);
map2:=map^(-1);
phi:=Ktx  ![map2(j):j in Coefficients(psi)];
level:=rec<TypeLevel| 
Phi:=phi, V:=0, prode:=1, prodf:=Degree(psi), omega:=power, cuttingslope:=0, Refinements:=[**], 
logPi:=Vector([1,0]), logPhi:=Vector([0,1]), PolynomialGenerator:=p, Pol:=Pol, Phiadic:=[Ktx!0,Ktx!0,Ktx!0,Ktx!0],
sfl:=[0,0,0,0]>;

level`Fq,level`map:=ResidueClassField(psi);
level`Redmap:=map;

if level`prodf gt 1 then  
 /*   mmm,nnn:=HasAttribute(level`Fq,"PowerPrinting");
    if mmm and nnn then 
	AssertAttribute(level`Fq, "PowerPrinting", false); 
    end if;*/

    level`z:=(level`Fq).1;
    AssignNames(~(level`Fq),["z" cat IntegerToString(0)]);
else

    level`z:=-Coefficient(psi,0);
end if;
level`FqY:=PolynomialRing(level`Fq:Global:=false);
AssignNames(~(level`FqY),["Y" cat IntegerToString(0)]);
if BAS then 
    level`ProdQuots:=[Ktx.1^k: k in [0..level`prodf-1]];
    level`ProdQuotsVals:=[Rationals()!0:k in [1..level`prodf]];
end if;
return level;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic PrescribedValue(~type,value,~Psi,~logpsi)
{if type is attached to the prime ideal P with Okutsu depth r, then logpsi=[a_0,...,a_r] and Psi=phi_1^a_1...phi_r^a_r, with v_P(p^a_0Psi(theta))=value}

Psi:=PolynomialRing(Parent(type[1]`PolynomialGenerator))!1;
logpsi:=RSpace(Integers(),#type)!0;
qq,val:=Quotrem(value,type[#type]`prode);
logpsi[1]:=qq;
if val gt 0 then
    body:=val;
    for k:=#type-1 to 1 by -1 do
	jj:=type[k]`invh*body mod type[k]`e;
	logpsi[k+1]:=jj;
	Psi*:=type[k]`Phi^jj;
	res:=(body-jj*type[k]`h) div type[k]`e;
	body:=res-jj*type[k]`V;
    end for;
    logpsi[1]+:=res;
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic CrossedValues(~K,p)
{Rows of Mat indexed by phi_Q and columns by w_P:=v_P/e(P/p)
}

for tree in K`TreesIntervals[p] do
    position:=tree[1]-1;
    Mat:=Matrix(Rationals(),#tree,#tree,[]);
    for j:=1 to #tree-1 do
	t1:=position+j;
	m1:=Degree(K`PrimeIdeals[p,t1]`Type[#K`PrimeIdeals[p,t1]`Type]`Phi);
	for k:=j+1 to #tree do
	    t2:=position+k;
	    inc:=0;
	    IndexOfCoincidence(~K`PrimeIdeals[p,t1]`Type,~K`PrimeIdeals[p,t2]`Type,~inc);
	    Ref1:=Append(K`PrimeIdeals[p,t1]`Type[inc]`Refinements,[* K`PrimeIdeals[p,t1]`Type[inc]`Phi,K`PrimeIdeals[p,t1]`Type[inc]`slope *]);
	    Ref2:=Append(K`PrimeIdeals[p,t2]`Type[inc]`Refinements,[* K`PrimeIdeals[p,t2]`Type[inc]`Phi,K`PrimeIdeals[p,t2]`Type[inc]`slope *]);
	    minlength:=Min(#Ref1,#Ref2);
	    ii:=2;
	    while ii le minlength and Ref1[ii,1] eq Ref2[ii,1] do 
		ii+:=1;    
	    end while;
	    minslope:=Min([Ref1[ii-1,2],Ref2[ii-1,2]]);
	    entry:=(K`PrimeIdeals[p,t1]`Type[inc]`V+minslope)/(K`PrimeIdeals[p,t1]`Type[inc]`prode*Degree(K`PrimeIdeals[p,t1]`Type[inc]`Phi));
	    Mat[k,j]:=Degree(K`PrimeIdeals[p,t2]`Type[#K`PrimeIdeals[p,t2]`Type]`Phi)*entry;
	    Mat[j,k]:=m1*entry;
	end for;
    end for;
    for t in tree do
	K`PrimeIdeals[p,t]`CrossedValues:=RowSequence(Mat)[t-position];
    end for;
end for;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic Taylor(pol::RngUPolElt,phi::RngUPolElt,omega::RngIntElt)->SeqEnum
{Compute the first omega+1 coefficients of the phi-expansion of pol}
quot:=pol;
Coeffs:=[];
Quos:=[];
for j:=0 to omega do 
  	quot,rem:=Quotrem(quot,phi);
  	Append(~Coeffs,rem);
	Append(~Quos,quot);
end for;
Prune(~Quos);
return Coeffs,Quos;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Newton(r,type,pol) -> SeqEnum
{Given a type of order at least r, and a polynomial, compute the
list of sides of the r-th order Newton polygon w.r.t. the type
}

phiadic:=Taylor(pol,type[r]`Phi,Floor(Degree(pol)/Degree(type[r]`Phi)));

sides:=[];
devs:=[* *];
Newton(r,~type,~phiadic,~sides,~devs);
return sides;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////


intrinsic LastLevel(Phiadic,~type,side,dev: Lastpsi:=true)
{in type[1]`sfl[1] we store the exponent of the irreducible factor}

ord:=#type;
type[ord]`e:=1;
if ord gt 1 then 
    nur:=&+[type[j]`slope/type[j]`prode: j in [1..ord-1]]; 
    type[1]`sfl[1]:=Floor((type[ord]`V/type[ord]`prode)-nur);
end if;
if side[2] eq 0 then
    slope:=-side[1];
    type[ord]`h:=Integers()!slope;
    type[1]`Phiadic[1]:=Phiadic[1];
    type[1]`Phiadic[2]:=Phiadic[2];
    if Lastpsi then
	psi:=0;
	ResidualPolynomial(ord,~type,~dev,~psi);
	type[ord]`psi:=psi/LeadingCoefficient(psi);
	type[ord]`logGamma:=type[ord]`logPhi-type[ord]`h*type[ord]`logPi;
    end if;
else
    slope:=Infinity();
end if;
type[ord]`slope:=slope;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic ResidualPolynomial(i,~type,~devsSide,~psi)
{Internal procedure to compute the i-th residual polynomial psi with respect to
a side S  of slope -type[i]`slope of the Newton polygon of a certain polynomial Pol. 
The coefficients of Pol whose attached  points in N_i(Pol) lie on S have multiadic expansions 
contained in the list devsSide.
}
	
require i le #type: "the first input is too large";
pj:=0;
rescoeffs:=[type[i]`Fq!0 : j in [1..#devsSide-1]];
if i eq 1 then
    height:=devsSide[#devsSide,2];
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not dev eq 0 then
	  
	map:=type[1]`Redmap;
		FPP:=Codomain(map);
	    tmp:=PolynomialRing(FPP)![map(ii):ii in Eltseq((dev 	div type[1]`PolynomialGenerator^height))];	
	    rescoeffs[j]:=Evaluate(tmp,type[i]`z);
	end if;
    height:=height-type[i]`h;
    end for;
else
    lprime:=(1-type[i-1]`invh*type[i-1]`h) div type[i-1]`e;
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not #dev eq 0 then
	    txp:=lprime*dev[#dev,1]-type[i-1]`invh*dev[#dev,2];
	    ResidualPolynomial(i-1,~type,~dev,~pj);
	    rescoeffs[j]:=type[i]`z^txp*Evaluate(pj,type[i]`z);
	end if;
    end for;
end if;
psi:=type[i]`FqY!rescoeffs;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////

intrinsic ResidualPolynomial(i,~type,~devsSide,~psi)
{Internal procedure to compute the i-th residual polynomial psi with respect to
a side S  of slope -type[i]`slope of the Newton polygon of a certain polynomial Pol. 
The coefficients of Pol whose attached  points in N_i(Pol) lie on S have multiadic expansions 
contained in the list devsSide.
}
	
require i le #type: "the first input is too large";
pj:=0;
rescoeffs:=[type[i]`Fq!0 : j in [1..#devsSide-1]];
if i eq 1 then
    height:=devsSide[#devsSide,2];
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not dev eq 0 then
	  
	map:=type[1]`Redmap;
		FPP:=Codomain(map);
	    tmp:=PolynomialRing(FPP)![map(ii):ii in Eltseq((dev 	div type[1]`PolynomialGenerator^height))];	
	    rescoeffs[j]:=Evaluate(tmp,type[i]`z);
	end if;
    height:=height-type[i]`h;
    end for;
else
    lprime:=(1-type[i-1]`invh*type[i-1]`h) div type[i-1]`e;
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not #dev eq 0 then
	    txp:=lprime*dev[#dev,1]-type[i-1]`invh*dev[#dev,2];
	    ResidualPolynomial(i-1,~type,~dev,~pj);
	    rescoeffs[j]:=type[i]`z^txp*Evaluate(pj,type[i]`z);
	end if;
    end for;
end if;
psi:=type[i]`FqY!rescoeffs;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////

intrinsic Localize(alpha,p)->RngIntElt,RngIntElt,RngUPolElt
{output=den,exp,Pol such that alpha = (1/den)*Pol(theta)*p^exp, and den is coprime to p}

if alpha eq 0 then 
    return 1,0,PolynomialRing(Integers())!0;
end if;
num:=[Parent(p)!i:i in Eltseq(Numerator(alpha))];
valnum:=Min([Valuation(x,p): x in num]);
Denom:=Parent(p)!Denominator(alpha);
valden:=Valuation(Denom,p);//h2
den:=Parent(p)!(Denom/p^valden);

return den,valnum-valden,PolynomialRing(Parent(p))!num div p^valnum;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic VValuation(pol:: RngUPolElt,poly:: RngUPolElt)->RngIntElt
{}
ord:=-1;
rem:=0;
pl:=pol;
while rem eq 0 do
    pl,rem:=Quotrem(pl,poly);
    ord+:=1;
end while;
return ord;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic ConvertLogs(~type,log,~class)
{log[1] is not used. The product of all Phi_i^log[i] for i>0 should have integer value M.
The output is the class of this product divided by p^M }
//wurde noch nicht Ã¼bersetzt.


vector:=log;
z:=0;
class:=PrimeField(type[1]`Fq)!1;
for i:=Degree(vector)-1 to 1 by -1 do
    ti:=vector[i+1] div type[i]`e;
    Z(~type,i,~z);
    class*:=z^ti;
    vector:=vector-ti*type[i]`logGamma;
    Truncate(~vector);
end for;
end intrinsic;

///////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic SFL(~type::SeqEnum,slope::RngIntElt)
{in type[1]`sfl and type[1]`Phiadic we stored relevant data. The aim is type[#type]`slope>=slope}
ord:=#type;
if type[ord]`slope ge slope then
    return;
end if;
//print"in SFL";
tts:=Realtime();
if type[1]`sfl[3] eq 0 then
    SFLInitialize(~type);
end if;
p:=type[1]`PolynomialGenerator;
exponent:=type[1]`sfl[1];
nu:=type[1]`sfl[2];
x0prec:=type[1]`sfl[3];
x0num:=type[1]`Phiadic[4];
x0den:=type[1]`sfl[4];
e:=type[ord]`prode;
h:=type[ord]`h-type[ord]`cuttingslope;

lasth:=slope-type[ord]`cuttingslope;

V:=type[ord]`V+type[ord]`cuttingslope;
//Zp:=pAdicRing(p,nu+exponent+Ceiling((V+2*lasth)/e));
precision:=nu+exponent+Ceiling((V+lasth)/e);
piZp:=p;
p_prec:=p^precision;
PolZp:=type[1]`Pol mod p_prec;		
PsinumZp:=type[1]`Phiadic[3] mod p_prec;
//zq:=quo<Zp|piZp^(nu+exponent+Ceiling((V+2*h)/e))>;
//zqt<t>:=PolynomialRing(zq);

path:=PathOfPrecisions(lasth,h);
shortpath:=PathOfPrecisions(h,x0prec);


newprecision:=nu+exponent+Ceiling(h/e);
p_prec_new:=p^newprecision;
a1:=type[1]`Phiadic[2] mod p_prec_new;

newprecision:=nu+exponent+Ceiling((V+path[2])/e);
p_prec_new:=p^newprecision;
phi:=type[ord]`Phi mod p_prec_new;
Psinum:= PsinumZp mod p_prec_new ;
A0num, A0den := reduce(p,((type[1]`Phiadic[1]mod p_prec_new)*Psinum) mod phi,nu);
A1num, A1den := reduce(p,((a1 mod p_prec_new)*Psinum) mod phi,nu);
for i in [2..#shortpath] do
    lowprecision:=A1den+2*x0den+Ceiling(shortpath[i]/e);
    Inversionloop(p,[* A1num,A1den *],~x0num,~x0den,phi,lowprecision);
end for;  

Anum, Aden := reduce(p,(A0num*(x0num mod p_prec_new)) mod phi, x0den+A0den);
phi:=phi+Anum;

for i in [2..#path-1] do

    loopprec:=nu+exponent+Ceiling((V+path[i+1])/e);
    ploop:=p^loopprec;
    phi:=phi mod ploop;

    Psinum:= PsinumZp mod ploop;
    qq,c0:=Quotrem(PolZp mod ploop,phi);
    c1:=qq mod phi;
    C0num,C0den := reduce(p,(c0*Psinum mod ploop) mod phi,nu);
    C1num,C1den := reduce(p,(c1*Psinum mod ploop) mod phi,nu);

    lowprecision:=C1den+2*x0den+Ceiling(path[i]/e);
    Inversionloop(p,[* C1num,C1den *],~x0num,~x0den,phi,lowprecision);

//PutInZ([(C0num*(x0num)mod ploop),ploop,phi]);
    Cnum,Cden:=reduce(p,(C0num*(x0num)mod ploop) mod phi, x0den+C0den);

    phi:=(phi+Cnum) mod ploop;

end for;

type[1]`sfl[3]:=Max([h,path[#path-1]]);

type[ord]`Phi:=phi mod p_prec;

type[1]`Phiadic[4]:=x0num;

type[1]`sfl[4]:=x0den;

end intrinsic;



///////////////////////////////////////////////////////////////



intrinsic InitialeModRing(R::RngUPol,q::RngUPolElt)->RngUPol
{}
A:=CoefficientRing(R);
quot<tt>:=quo<A|q>;
R<xx>:=PolynomialRing(quot);
return R;
end intrinsic;
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


intrinsic PutModRing(RMod::RngUPol,g::RngUPolElt)->RngUPol
{}

k:=BaseRing(CoefficientRing(Parent(g)));
A:=PolynomialRing(k);
Amod:=CoefficientRing(RMod);
return RMod![Amod!(A!i):i in  Eltseq(g)];


end intrinsic;


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

intrinsic ChangePrecMod(RMod::RngUPol,g::RngUPolElt)->RngUPol
{}
R:=BaseRing(RMod);
ll:=Eltseq(g);

return RMod![R!Eltseq(i):i in ll];


end intrinsic;

///////////////////////////////////////////////////////////////


intrinsic SFL2(~type::SeqEnum,slope::RngIntElt)
{in type[1]`sfl and type[1]`Phiadic we stored relevant data. The aim is type[#type]`slope>=slope}
ord:=#type;
if type[ord]`slope ge slope then
    return;
end if;
print"SFL2 with slope",slope;
tts:=Realtime();
if type[1]`sfl[3] eq 0 then
    SFLInitialize(~type);
end if;
p:=type[1]`PolynomialGenerator;
exponent:=type[1]`sfl[1];
nu:=type[1]`sfl[2];
x0prec:=type[1]`sfl[3];
x0num:=type[1]`Phiadic[4];
x0den:=type[1]`sfl[4];
e:=type[ord]`prode;
h:=type[ord]`h-type[ord]`cuttingslope;
lasth:=slope-type[ord]`cuttingslope;
V:=type[ord]`V+type[ord]`cuttingslope;
//Zp:=pAdicRing(p,nu+exponent+Ceiling((V+2*lasth)/e));
precision:=nu+exponent+Ceiling((V+lasth)/e);
piZp:=p;
p_prec:=p^precision;
PolZp:=type[1]`Pol;
Ax:=Parent(PolZp);
RMod:=InitialeModRing(Ax,p_prec);
PolZp:=PutModRing(RMod,PolZp);
	
PsinumZp:=PutModRing(RMod,type[1]`Phiadic[3] );

path:=PathOfPrecisions(lasth,h);
shortpath:=PathOfPrecisions(h,x0prec);

newprecision:=nu+exponent+Ceiling(h/e);

p_prec_new:=p^newprecision;
RMod:=InitialeModRing(Ax,p_prec_new);
a1:=PutModRing(RMod,type[1]`Phiadic[3] );

newprecision:=nu+exponent+Ceiling((V+path[2])/e);
p_prec_new:=p^newprecision;
RMod:=InitialeModRing(Ax,p_prec_new);
phi:=PutModRing(RMod,type[ord]`Phi );


Psinum:=PutModRing(RMod, PsinumZp);
ty_phad1:=PutModRing(RMod,type[1]`Phiadic[1]);
A0num, A0den := reduce2(p,(ty_phad1*Psinum) mod phi,nu);
a1:=ChangePrecMod(RMod,a1);
Psinum:=ChangePrecMod(RMod,Psinum);
phi:=ChangePrecMod(RMod,phi);
			//Parent(a1),Parent(Psinum);

A1num, A1den := reduce(p,(a1*Psinum) mod phi,nu);

for i in [2..#shortpath] do
    lowprecision:=A1den+2*x0den+Ceiling(shortpath[i]/e);
    Inversionloop2(p,[* A1num,A1den *],~x0num,~x0den,phi,lowprecision);
end for;  
print"done";
x0num:=PutModRing(RMod,x0num);
Anum, Aden := reduce(p,(A0num*x0num ) mod phi, x0den+A0den);
phi:=phi+Anum;

for i in [2..#path-1] do

    loopprec:=nu+exponent+Ceiling((V+path[i+1])/e);
    ploop:=p^loopprec;
    RMod:=InitialeModRing(Ax,ploop);
    phi:=ChangePrecMod(RMod,phi);
print"2",i;
    Psinum:= ChangePrecMod(RMod,PsinumZp);
    PolZp:=ChangePrecMod(RMod,PolZp);
    qq,c0:=Quotrem(PolZp,phi);
print"3",i;
    c1:=qq mod phi;
    C0num,C0den := reduce(p,(c0*Psinum ) mod phi,nu);
    C1num,C1den := reduce(p,(c1*Psinum) mod phi,nu);
print"4",i;
    lowprecision:=C1den+2*x0den+Ceiling(path[i]/e);
    Inversionloop2(p,[* C1num,C1den *],~x0num,~x0den,phi,lowprecision);
print"5",i;
//PutInZ([(C0num*(x0num)mod ploop),ploop,phi]);
    Cnum,Cden:=reduce(p,(C0num*x0num) mod phi, x0den+C0den);
print"6",i;
    phi:=phi+Cnum;
    print"7",i;
end for;
print"8";
type[1]`sfl[3]:=Max([h,path[#path-1]]);
print"9";
type[ord]`Phi:=phi;
print"10";
type[1]`Phiadic[4]:=x0num;
print"11";
type[1]`sfl[4]:=x0den;

end intrinsic;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

intrinsic SFL(~K::FldFun,~P::Rec,slope::RngIntElt)
{}

if P`Type[#P`Type]`slope ge slope then
    return;
end if;
SFL(~P`Type,slope);
UpdateLastLevel(~P`Type);
K`PrimeIdeals[P`PolynomialGenerator,P`Position]`Type[#P`Type]:=P`Type[#P`Type];
K`PrimeIdeals[P`PolynomialGenerator,P`Position]`Type[1]:=P`Type[1];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic SFLInitialize(~type)
{}

p:=type[1]`PolynomialGenerator;
r:=#type-1;
e:=type[r+1]`prode;
a1:=type[1]`Phiadic[2];
Psinum:=PolynomialRing(Parent(p))!1;
if r eq 0 then

    nu:=Min([Valuation(xx,p): xx in Coefficients(a1)]);
    helpa1:=PolynomialRing(type[1]`Fq)![type[1]`Redmap(i):i in Coefficients(a1 div p^nu)];

    class:=Evaluate(helpa1,type[1]`z);
else
    val:=0;
    dev:=[* *];
    Value(r+1,~type,a1,~dev,~val);
    respol:=0;
    ResidualPolynomial(r,~type,~dev,~respol);
    logpsi:=0;
    qq,s:=Quotrem(-val,e);
    PrescribedValue(~type,s,~Psinum,~logpsi);
    nu:=-logpsi[1]-qq;
    vector:=dev[#dev,1]*type[r]`logPhi+dev[#dev,2]*type[r]`logPi;
    class:=0;
    ConvertLogs(~type,logpsi+vector,~class);
    class*:=Evaluate(respol,type[r+1]`z);
end if;
type[1]`Phiadic[3]:=Psinum;
type[1]`sfl[2]:=nu;
type[1]`sfl[3]:=1;
x0num:=0;
x0den:=0;
LocalLift(~type,class^(-1),~x0num,~x0den);
type[1]`Phiadic[4]:=x0num;
type[1]`sfl[4]:=x0den;
end intrinsic;

///////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Value(i,~type,pol,~devs,~val)
{Given a level i, a type and a polynomial pol, the output is:
devs=multiexpansion with respect to phi_1,...,phi_i-1 of the points in S_lambda_i-1(pol)
val=i-th valuation of pol w.r.t. type}
//PutInZ([*i,type,pol,devs,val*]);
require i le #type+1: "the first input is too large";
val:=Infinity();
if pol eq 0 then
    if i eq 1 then
	  devs:=0;
    else
	  devs:=[];
    end if;
    return;
end if;
if i eq 1 then 
    val:=Min([Valuation(c,type[1]`PolynomialGenerator): c in Coefficients(Parent(type[1]`Phi)!pol)]);
    devs:=pol;
else  
    im1:=i-1;
    step:=type[im1]`V+type[im1]`slope;
//    print"step",step;
    minheight:=0;
    Vheight:=0;
    twoe:=2*type[im1]`e;
    quot:=pol;
    k:=0;
    last:=0;

    while quot ne 0 and minheight le val do
	dev:=[* *];
	newval:=0;
	quot,ak:=Quotrem(quot,type[im1]`Phi); // sollte man verbessern
        Value(im1,~type,ak,~dev,~newval);
	candidate:=newval+minheight;
//	  print"newval,minheight,im1",newval,minheight,im1;
	if candidate le val then
	    if candidate lt val then

		val:=candidate;
		

		firstabscissa:=k;
		firstordinate:=newval+Vheight;
		devs:=[* dev *];
	    else  
	    for jj:=last+twoe to k by type[im1]`e do;
		if im1 eq 1 then 
		    Append(~devs,0);
		else
		    Append(~devs,[]);
		end if;
	    end for;
	    Append(~devs,dev);
	    end if;
      	last:=k;
	end if;
	minheight+:=step;
	Vheight+:=type[im1]`V;
	//		print"changes",step, minheight,Vheight,type[im1]`V;
	k+:=1;
    end while;

    Append(~devs,[firstabscissa,firstordinate]);
    val:=Integers()!(type[im1]`e*val);
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic EqualizeLogs(~log1,~log2)
{}

d:=Degree(log1)-Degree(log2);
if d ne 0 then
    tail:=[0: i in [1..Abs(d)]];
    if d gt 0 then
	log2:=Vector(Eltseq(log2) cat tail);
    else
	log1:=Vector(Eltseq(log1) cat tail);
    end if;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Z(~type,i,~z)
{z=z_i belongs to F_(i+1)}

if i eq #type then 
    z:=-Coefficient(type[#type]`psi,0);
else
    z:=type[i+1]`z;
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IndexOfCoincidence(~t1,~t2,~i)
{the types must correspond to different prime ideals}

require t1[1]`PolynomialGenerator eq t2[1]`PolynomialGenerator: "types attached to different prime numbers";
if t1[1]`Phi mod t1[1]`PolynomialGenerator ne t2[1]`Phi mod t1[1]`PolynomialGenerator then 
    i:=0;
else

i:=1;
while t1[i]`Phi eq t2[i]`Phi and t1[i]`slope eq t2[i]`slope and t1[i]`psi eq t2[i]`psi do
    i+:=1;
end while;	
end if;

end intrinsic;

intrinsic IndexOfCoincidence(t1::Rec, t2::Rec)-> RngIntElt
    { The index of coincidence of types t1 and t2. }

    i := 0;
    IndexOfCoincidence(~t1`Type, ~t2`Type, ~i);

    return i;
end intrinsic;

intrinsic IndexOfCoincidence(t1::SeqEnum, t2::SeqEnum)-> RngIntElt
    { }

    i := 0;
    IndexOfCoincidence(~t1, ~t2, ~i);

    return i;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic PathOfPrecisions(n,h) -> SeqEnum
{}

q:=n;
precs:=[n];
while q gt h do
    q,a:=Quotrem(q,2);
    q+:=a;
    Append(~precs,q);
end while;
return Reverse(precs);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic reduce(p,poly,den)->RngUPolElt,RngIntElt
{}

if poly eq 0 then
    return poly,0;
end if;
cancel:=Min([den,Min([Valuation(Parent(p)!a,p):a in Eltseq(poly)])]);

num:=poly div p^cancel;

//ChangePrecision(~num,GetPrecision(Zp));
return num,den-cancel;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic reduce2(p,poly,den)->RngUPolElt,RngIntElt
{}

if poly eq 0 then
    return poly,0;
end if;
cancel:=Min([den,Min([Valuation(Parent(p)!a,p):a in Eltseq(poly)])]);

num:=poly div p^cancel;

//ChangePrecision(~num,GetPrecision(Zp));
return num,den-cancel;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Inversionloop(p,A,~xnum,~xden,phi,precision)
{}
anum:=A[1];
aden:=A[2];
pi:=p;
//zqq:=quo<Zp|pi^precision>;
piq:=p;
//zqqt<t>:=PolynomialRing(zqq);

Phip:=phi mod pi^precision; 
xnum :=xnum mod pi^precision;
x1num,x1den:=reduce(p,(2*piq^(xden+aden)-((anum mod pi^precision)*xnum)mod pi^precision) mod Phip,xden+aden); 
xnum,xden:=reduce(p,((xnum*x1num) mod pi^precision) mod Phip, xden+x1den);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Inversionloop2(p,A,~xnum,~xden,phi,precision)
{}
anum:=A[1];
aden:=A[2];

Phip:=phi ; 
R:=BaseRing(Parent(phi));
piq:=Parent(phi)!(R!p);
xnum :=PutModRing(Parent(phi),xnum);
//x1num:=PutModRing(Parent(phi),x1num);

x1num,x1den:=reduce(p,(2*piq^(xden+aden)-((anum )*xnum)) mod Phip,xden+aden); 
xnum,xden:=reduce(p,((xnum*x1num)) mod Phip, xden+x1den);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic UpdateLastLevel(~type)
{}


qq,a0:=Quotrem(type[1]`Pol,type[#type]`Phi);

if a0 eq 0 then 
    type[#type]`slope:=Infinity();
else    
    type[1]`Phiadic[1]:=a0;

    type[1]`Phiadic[2]:=qq mod type[#type]`Phi;

    sides:=[];
    devs:=[* *];
    tmp:=[a0,type[1]`Phiadic[2]];
    Newton(#type,~type,~tmp,~sides,~devs);

    type[#type]`slope:=-sides[1,1];
    type[#type]`h:=-Integers()!sides[1,1];
    psi:=0;
    ResidualPolynomial(#type,~type,~devs[1],~psi);

    type[#type]`psi:=psi/LeadingCoefficient(psi);
    type[#type]`logGamma:=type[#type]`logPhi-type[#type]`h*type[#type]`logPi;
 
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic LocalLift(~type,class,~numlift,~denlift)
{class should belong to the residue class field  type[r]`Fq. 
The output is a pair g,e such that g(theta)/p^e is a lift to a P-integral element in K
and deg g(x)<n_P}

require class in type[#type]`Fq: "Second argument must lie in the residue field of first argument";
i:=1;
while class notin type[i]`Fq do
	i+:=1;
end while;
if i eq 1 then 
    p:=type[1]`PolynomialGenerator;
	mappitemp:=type[1]`Redmap;
	Ftemp:=Codomain(mappitemp);
	mappi:=mappitemp^(-1);
	numlift:= PolynomialRing(Parent(p))![mappi(j):j in Eltseq(class,Ftemp)];
	denlift:=0;
else
    expden:=Ceiling(type[i]`V/type[i]`prode);
    V:=type[i]`prode*expden;
    log:=V*type[i]`logPi;
    newclass:=0;
    ConvertLogs(~type,log,~newclass);
    H:=V div type[i-1]`e;
    elt:=type[i]`z^(type[i-1]`invh*H)*class*newclass^(-1);
    varphi:=type[i-1]`FqY!Eltseq(type[i]`Fq!elt,type[i-1]`Fq);
    lift:=0;
    Construct(i-1,~type,varphi,0,H,~lift);
    v1lift:=Min([Valuation(x,type[1]`PolynomialGenerator): x in Coefficients(lift)]);
    numlift:=lift div type[1]`PolynomialGenerator^v1lift;
    denlift:=expden-v1lift;
end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic LocalLift(class,P)->FldFunElt
{class should belong to the residue class field Z_K/P. 

The output is a lift to a P-integral element in K}

numlift:=0;
denlift:=0;
LocalLift(~P`Type,class,~numlift,~denlift);
return  Evaluate(P`Parent,numlift)/P`PolynomialGenerator^denlift;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////


intrinsic Construct(i,~type,respol,s,u,~Ppol)
{This routine constructs a polynomial Ppol with integer coefficients such that: 
deg Ppol<m_i+1 and y^nu*R_i(Ppol)(y)=respol(y), where nu=ord_y(respol).
The non-negative integers s,u are the coordinates of the left endpoint of a segment of slope -type[i]`slope supporting N_i(Ppol).
}

require i le #type: "the first input is too large";
require Degree(respol) lt type[i]`f: "the Degree of the 3rd argument is too large"; 
require u+s*type[i]`slope ge type[i]`f*(type[i]`e*type[i]`V+type[i]`h): "the point (s,u) is too low";
var:=type[i]`Phi^type[i]`e;
Ppol:=0;
if i eq 1 then
	height:=u-Degree(respol)*type[i]`h;
	p:=type[1]`PolynomialGenerator;
	mappitemp:=type[1]`Redmap;
	Ftemp:=Codomain(mappitemp);
	mappi:=mappitemp^(-1); 
    for a in Reverse(Coefficients(respol)) do
	lift:= PolynomialRing(Parent(p))![mappi(j):j in Eltseq(a,Ftemp)]; 
	Ppol:=Ppol*var+lift*type[1]`PolynomialGenerator^height;
	height:=height+type[1]`h;
    end for; 
else	
    step:=type[i]`e*type[i]`V+type[i]`h;
    newV:=u-Degree(respol)*step-s*type[i]`V;
    im1:=i-1;
    for a in Reverse(Coefficients(respol)) do
	Pj:=0;
	if a ne 0 then
	    txp,sa:=Quotrem(type[im1]`invh*newV,type[im1]`e);
	    ua:=(newV-sa*type[im1]`h) div type[im1]`e; 
	    newrespol:=type[im1]`FqY!Eltseq(a*type[i]`z^txp,type[im1]`Fq);
	    Construct(im1,~type,newrespol,sa,ua,~Pj);
	end if;
	Ppol:=Ppol*var+Pj;
	newV:=newV+step;
    end for;
end if;        
Ppol:=Ppol*type[i]`Phi^s;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic Newton(i,~type,~phiadic,~sides,~devsEachSide)
{Given a type of order at least i, and the phiadic expansion of a polynomial, compute:
sides=list of sides of the r-th order Newton polygon w.r.t. the type, and 
devsEachSide[k]=list of multiadic phi_1,...,phi_i-1 expansion of the coefficients of the polynomial whose attached point lies on sides[k]}

require i le #type: "the first input is too large";
n:=0;
cloud:=[];
devsEachSide:=[* *];
alldevs:=[* *];
for k in [1..#phiadic] do 
        val:=0;
        dev:=[* *];
        Value(i,~type,phiadic[k],~dev,~val);
        if IsFinite(val) then 
	    Append(~cloud,<k-1,val+n>);  
	    Append(~alldevs,dev);
        end if;
        n+:=type[i]`V;
end for;
V:=NewtonPolygon(cloud);
s:=LowerVertices(V);
sides:=[[LowerSlopes(V)[k],s[k,1],s[k,2],s[k+1,1],s[k+1,2]]: k in [1..#LowerSlopes(V)]];
abscissas:=[x[1] : x in cloud];
for sd in sides do
    height:=Integers()!sd[3];
    dev:=[* *];
    for jj:=Integers()!sd[2] to Integers()!sd[4] by Denominator(sd[1]) do 
	position:=Index(abscissas,jj);
	if position gt 0 and cloud[position,2] eq height then
	    Append(~dev,alldevs[position]);
	else
	    if i eq 1 then
		Append(~dev,0);
	    else
		Append(~dev,[]);
	    end if;
	end if;
	height:=height+Numerator(sd[1]);  
    end for;
    Append(~dev,[Integers()!sd[2],Integers()!sd[3]]);
    Append(~devsEachSide,dev);
end for;
if #sides eq 0 then
      sides:=[[0,s[1,1],s[1,2],s[1,1],s[1,2]]];
      devsEachSide:=[* alldevs[Index(abscissas,Integers()!s[1,1])],[Integers()!s[1,1],Integers()!s[1,2]] *];
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic '*'(I::Rec ,J:: Rec)->Rec
{Compute the product  of the  fractional ideals I,J. They are both factored if their factorization is not yet known.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I) : "First argument is neither an IdealRecord nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(J): "Second argument is neither an IdealRecord nor a PrimeIdealRecord";
require I`Parent eq J`Parent: "Ideals do not belong to the same function field";
if IsZero(I) then return I; end if;
if IsZero(J) then return J; end if;
list:= Sort2(Factorization(I) cat Factorization(J));
tot:=#list;
output:=[];
pos:=1;
while pos le tot do    
    i:=pos+1;
    term:=list[pos];
    if (i le tot and list[i,1] eq term[1] and list[i,2] eq term[2]) then 
        term[3]+:=list[i,3];
        i:=i+1;
    end if;
    Append(~output,term);
    pos:=i;
end while;
output:=SequenceToList([x: x in output | x[3] ne 0]);
id:= rec<IdealRecord|  Factorization:= output,
                       FactorizationString:= FactorListToString(output), 
                       Parent:=I`Parent,
                       IsPrime:=(#output eq 1 and output[1,3] eq 1)>;
return id;
end intrinsic;

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

intrinsic '^'(I::Rec, n::RngIntElt)->Rec
{Compute the n-th power of the fractional ideal I. The ideal I is factored if it is not already known its factorization. }
require IsIdealRecord(I) or IsPrimeIdealRecord(I) : "Argument is neither an IdealRecord nor a PrimeIdealRecord";
require not IsZero(I) or n ge 0 : "The zero ideal is not invertible";

if IsZero(I) then return I; end if;
//if n eq 1 then return I; end if;
if n eq 0 then return  rec<IdealRecord|
                            Parent:=I`Parent, 
                            Generators:=[I`Parent!1],
                            Factorization:=[* *],
                            FactorizationString:=""  >; 
end if;

l:=Factorization(I);
for i in [1..#l] do l[i,3]:=n*l[i,3]; end for;
id:= rec<IdealRecord|
                Parent:=I`Parent, 
                Factorization:=l,
                FactorizationString:=FactorListToString(l),
                IsPrime:=(#l eq 1 and l[1,3] eq 1)>;
if assigned id`Generator and n gt 0 then
    TwoElement(~id);
end if;
return id;
end intrinsic;

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

intrinsic FactorListToString(list)->MonStgElt
{Technical function to write down a factorization in pretty form. For internal use only}
if #list eq 0 then return ""; end if;
str:="";
for x in list do
  str:=str cat Sprintf( "*P(%o,%o)", x[1],x[2]);
  if x[3] ne 1 then str:=str cat Sprintf("^%o",x[3]); end if;
end for;
return Substring(str,2,#str);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IsZero(I::Rec )-> BoolElt
{True iff I is the zero ideal}
require IsPrimeIdealRecord(I) or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 
if IsPrimeIdealRecord(I) then return false; end if;
return assigned I`Generators and &and[x eq 0: x in I`Generators];
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Factorization(I::Rec)->SeqEnum
{Compute the decomposition of the fractional ideal I into prime ideals.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "Argument is neither an IdealRecord record nor a PrimeIdealRecord";
if IsIdealRecord(I) then 
    Factorization(~I);
    return I`Factorization;
else
    return [*[*I`PolynomialGenerator,I`Position,1*]*];
end if; 
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Factorization(~I::Rec)
{Compute the decomposition of the fractional ideal I into prime ideals.}
require IsIdealRecord(I): "Argument should be an IdealRecord record.";
if not assigned I`Factorization then 
    require not IsZero(I): "Argument should be a non-zero ideal.";
    I`Factorization:=[* *];
    K:=I`Parent;
    Rt:=PolynomialRing(ConstantField(K));
    Rxt:=PolynomialRing(Rt);
    normradicals:=[];
    nums:=[];
    dens:=[];
    betas:=[];
    primes:={};
    for g in I`Generators do
        coefs:=Eltseq(g,BaseRing(Parent(g)));
        den:=[Rt!Denominator(x): x in coefs];
        primes:=primes join &join[Set([i[1]:i in Factorization(x)]): x in den];
        num:=Numerator(g); 
       
        gcd:=GCD([Rt!i:i in Eltseq(num)]);
        beta:=num/gcd;
        Append(~betas,beta);
        Append(~normradicals,
            gcd*Resultant(Rxt!Eltseq(beta),Rxt!DefiningMonicPolynomial(K)));
        Append(~dens,LCM(den));
        Append(~nums,gcd);
    end for;

    temp:=GCD([Rt!i:i in normradicals]);
    primes:=Sort(SetToSequence(primes join Set([i[1]:i in Factorization(temp)])));
    for p in primes do
        h1:=[Valuation(x,p): x in nums];
        h2:=[Valuation(x,p): x in dens];
        Montes(K,p);
        for j in [1..#K`PrimeIdeals[p]] do
            P:=K`PrimeIdeals[p,j];
            h:=[PValuation(x,P): x in betas];
            exp:=Min([(h1[i]-h2[i])*P`e+h[i]: i in [1..#h1]]);
            if exp ne 0 then 
                Append(~I`Factorization,[*p,j,exp*]);
            end if;    
        end for;
    end for;
    I`FactorizationString:=FactorListToString(I`Factorization);
    I`IsPrime:=(#I`Factorization eq 1 and I`Factorization[1,3] eq 1) ;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Representative(~type)
{Construction of a representative phi of a type. 
We add phi and V at a new level of type}

s:=#type;
ef:=type[s]`e*type[s]`f;        
u:=ef*type[s]`V+type[s]`f*type[s]`h;                
newphi:=0;
Construct(s,~type,Reductum(type[s]`psi),0,u,~newphi);                   
newphi+:=type[s]`Phi^ef;          
newlevel:=rec<TypeLevel| 
Phi:=newphi, 
V:=type[s]`e*u, 
cuttingslope:=0, 
Refinements:=[* *],
prode:=type[s]`prode*type[s]`e,
prodf:=type[s]`prodf*type[s]`f,
Fq:=ext<type[s]`Fq| type[s]`psi>
>;
newlevel`FqY:=PolynomialRing(newlevel`Fq:Global:=false);
AssignNames(~(newlevel`Fq),["z" cat IntegerToString(s)]);
AssignNames(~(newlevel`FqY),["Y" cat IntegerToString(s)]);
if type[s]`f gt 1 then
    newlevel`z:=newlevel`Fq.1;
else
    newlevel`z:=-Coefficient(type[s]`psi,0);                                              
end if;             
Append(~type,newlevel);
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic ResidualPolynomial(i,~type,~devsSide,~psi)
{Internal procedure to compute the i-th residual polynomial psi with respect to
a side S  of slope -type[i]`slope of the Newton polygon of a certain polynomial Pol. 
The coefficients of Pol whose attached  points in N_i(Pol) lie on S have multiadic expansions 
contained in the list devsSide.
}
//PutInZ([*type,i,devsSide,psi*]);  
//print"\n\n in ResidualPolynomial with \n\n",i,	devsSide;
require i le #type: "the first input is too large";
pj:=0;
rescoeffs:=[type[i]`Fq!0 : j in [1..#devsSide-1]];
if i eq 1 then
    height:=devsSide[#devsSide,2];
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not dev eq 0 then
	  
	map:=type[1]`Redmap;
		FPP:=Codomain(map);
	    tmp:=PolynomialRing(FPP)![map(ii):ii in Eltseq((dev 	div type[1]`PolynomialGenerator^height))];	
	    rescoeffs[j]:=Evaluate(tmp,type[i]`z);
	end if;
    height:=height-type[i]`h;
    end for;
else
    lprime:=(1-type[i-1]`invh*type[i-1]`h) div type[i-1]`e;
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not #dev eq 0 then
	    txp:=lprime*dev[#dev,1]-type[i-1]`invh*dev[#dev,2];
//	    print"in put respol",i-1,dev;	
  
	    ResidualPolynomial(i-1,~type,~dev,~pj);
	    rescoeffs[j]:=type[i]`z^txp*Evaluate(pj,type[i]`z);
//	    print"\n\n res pol",rescoeffs[j];	    
	end if;
    end for;
end if;
psi:=type[i]`FqY!rescoeffs;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Inverse(M::AlgMatElt,d::FldFunRatUElt)->AlgMatElt
{Speeds up inversion of a matrix over the rational function field}

K:=BaseRing(M);
R:=PolynomialRing(ConstantField(K));
Mpol:=ChangeRing(d*M,R);
H,R:=HermiteForm(Mpol);
return d*ChangeRing(H,K)^-1*R;
end intrinsic;

///////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic RRSpace(~D::Rec:Reduced:=false)
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one if
Reduced:=true. No divisorreduction is applied}

if Reduced and assigned D`RedBasis then return; end if;
if not Reduced and assigned D`SRedBasis then return; end if;
//if assigned D`SmallDiv then tmp:=Reduced;RRSpace2(~D:Reduced:=tmp);	return; end if;
Ifin:=D`FiniteIdeal;	Iinf:=D`InfiniteIdeal;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;
//////////////////////////Producing bases/////////////////////////
Bfin,finitefac:=IdealBase(Ifin);
Montes(F2,t);

InfPrimes:=PrimesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;
if Reduced eq true then
	Binf,Values,_,_,_,infex:=pBasisRed(Iinf,t:Reduced:=true);	
else
	Binf,_,_,_,_,infex:=pBasis(Iinf,t);
end if;
Bprime:=[TranslationMap(i,F):i in Binf];
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);
M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);

if Reduced eq true then
	denmax:=K!Sort([Denominator(i):i in Bprime])[n];
	Mhelp:=Inverse(M2,denmax);
else
	Mhelp:=M2^(-1);
end if;

T:=M1*Mhelp;

if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T,Values);

else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T);
end if;	

if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([deg(j):j in i]):i in RowSequence(T)];

	redbasis:=[i*finitefac:i in Bfin];
	SuccMin:=[Deg(K!finitefac)+i+infex:i in SuccMin];
else	
	redbasis:=[finitefac * &+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
	SuccMin:=[i+infex+Deg(K!finitefac):i in SuccMin];

end if;

if Reduced eq true then
	D`RedBasis:=redbasis;
	D`SuccessiveMinima:=SuccMin;
else	
	D`SRedBasis:=redbasis;
	D`ApproximatedSuccessiveMinima:=SuccMin;
end if;

end intrinsic;



///////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*

intrinsic RRSpace_no_disc(~D::Rec:Reduced:=false)
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one if
Reduced:=true. No divisorreduction is applied}

if Reduced and assigned D`RedBasis then return; end if;
if not Reduced and assigned D`SRedBasis then return; end if;
//if assigned D`SmallDiv then tmp:=Reduced;RRSpace2(~D:Reduced:=tmp);	return; end if;
Ifin:=D`FiniteIdeal;	Iinf:=D`InfiniteIdeal;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;
//////////////////////////Producing bases/////////////////////////
Bfin,finitefac:=IdealBaseNoDisc(Ifin);
Montes(F2,t);

InfPrimes:=PrimesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;
if Reduced eq true then
	Binf,Values,_,_,_,infex:=pBasisRed(Iinf,t:Reduced:=true);	
else
	Binf,_,_,_,_,infex:=pBasis(Iinf,t);
end if;
Bprime:=[TranslationMap(i,F):i in Binf];
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);
M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);

if Reduced eq true then
	denmax:=K!Sort([Denominator(i):i in Bprime])[n];
	Mhelp:=Inverse(M2,denmax);
else
	Mhelp:=M2^(-1);
end if;

T:=M1*Mhelp;

if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T,Values);

else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T);
end if;	

if NumberOfRedSteps eq 0 then	

	redbasis:=[i*finitefac:i in Bfin];
	SuccMin:=[Deg(K!finitefac)+i+infex:i in SuccMin];
	
else	
	redbasis:=[finitefac * &+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
	SuccMin:=[i+infex+Deg(K!finitefac):i in SuccMin];

end if;

if Reduced eq true then
	D`RedBasis:=redbasis;
	D`SuccessiveMinima:=SuccMin;
else	
	D`SRedBasis:=redbasis;
	D`ApproximatedSuccessiveMinima:=SuccMin;
end if;

end intrinsic;



///////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////



intrinsic RRSpace(D::Rec:Reduced:=false)->ModMatRngElt
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one if
Reduced:=true. No divisorreduction is applied}

//if Reduced and assigned D`RedBasis then return; end if;
//if not Reduced and assigned D`SRedBasis then return; end if;
//if assigned D`SmallDiv then tmp:=Reduced;RRSpace2(~D:Reduced:=tmp);	return; end if;
Ifin:=D`FiniteIdeal;	Iinf:=D`InfiniteIdeal;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;
//////////////////////////Producing bases/////////////////////////
Bfin,finitefac:=IdealBase(Ifin);
Montes(F2,t);

InfPrimes:=PrimesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;
if Reduced eq true then
	Binf,Values,_,_,_,infex:=pBasisRed(Iinf,t:Reduced:=true);	
else
	Binf,_,_,_,_,infex:=pBasis(Iinf,t);
end if;
Bprime:=[TranslationMap(i,F):i in Binf];
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);
M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);

if Reduced eq true then
	denmax:=K!Sort([Denominator(i):i in Bprime])[n];
	Mhelp:=Inverse(M2,denmax);
else
	Mhelp:=M2^(-1);
end if;

T:=M1*Mhelp;

if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T,Values);

else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T);
end if;	
return T,RedT;



end intrinsic;
*/

/////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic RRSpace2(~D::Rec:Reduced:=false)
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one of
Reduced:=true.}

F:=D`FiniteIdeal`Parent;

if F`ReductionON eq false and not assigned D`r then 
	RRSpace(~D); 
else 

	if not assigned D`r then
		DivisorReduction(~D);
	end if;	
	Dtmp:=D`SmallDiv;	r:=D`r;	a:=D`a;

		if Reduced then

			RRSpace(~Dtmp:Reduced:=true);
			redbasistmp:=Dtmp`RedBasis;	
			SuccMin:=Dtmp`SuccessiveMinima;
		else
			RRSpace(~Dtmp);	
			redbasistmp:=Dtmp`SRedBasis;
			SuccMin:=Dtmp`ApproximatedSuccessiveMinima;	
		end if;

	redbasis:=[ a* i:i in redbasistmp];

	if Reduced then
		print"what";
		D`RedBasis:=redbasis;	D`SuccessiveMinima:=[i+r:i in SuccMin];
	else
		D`SRedBasis:=redbasis;	D`ApproximatedSuccessiveMinima:=[i+r:i in SuccMin];
	end if;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IdealBase(I::Rec:Maximal:=false)->SeqEnum
    {Compute a Hermite basis of the ideal I}

//if not assigned I`Basis then
	F:=I`Parent;	kt:=PolynomialRing(ConstantField(F));
	    tt:=Realtime();
	if #I`Factorization eq 0 then Maximal:=true; end if;
    if not assigned F`FactorizedDiscriminant then
 		d:=kt! Discriminant(DefiningMonicPolynomial(F));   
    	sq:=SquarefreeFactorization(d);
		d:=kt!(d/&*[i[1]:i in sq]);
		print"disc is now square free (IdealBaseRR)",Realtime()-tt;
    	F`FactorizedDiscriminant:=Factorization(d);
    end if;
    if not assigned F`Index then
    	tt:=Realtime();
    	_:=Index(F);
    //	print"IndEx in IdealBaseRR",Realtime()-tt;
    end if;
   	if Maximal eq true then
   		if not assigned F`IndexBases then
   		F`IndexBases:=[];
	    base:= SIdealBase(I, F`Index:Maximal:=true);
   		return base,1;   	
   		end if;
   	end if; 
    
	primes:=SetToSequence(Set(RationalRadical(I) cat F`Index));

    if primes eq [] then
    	return [F.1^i:i in [0..Degree(F)-1]],1;
    end if;
 //   print"Ideal infos",#primes,[Degree(i):i in primes];
    base,fac:= SIdealBase(I, primes);
	return base,fac;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IdealBasis(I::Rec:MaxMin:=true)->SeqEnum
    {Computes a Hermite basis of the ideal I with the MaxMin-method if MaxMin=true else use Multipliers}

if MaxMin then
	return idealBasis(I);
else
	return IdealBase(I);
end if;	
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic Index(K::FldFun)->SeqEnum
{Compute the index of the maximal order O_K over the equation order of K and 
factorizes the discriminant of K.}

if not assigned K`Index then 
	kt<t>:=PolynomialRing(ConstantField(K));

	t1:=Realtime();
 	if not assigned K`FactorizedDiscriminant then
 		 		
 		d:=kt!Discriminant(DefiningPolynomial(K));
 		if IsFinite(ConstantField(K)) then
 		
			sq:=SquarefreeFactorization(d);
			if not #sq eq 0 then 
				d:=kt!(d/&*[i[1]:i in sq]);
			end if;	
			
		else 
			d:=GCD(d,Derivative(d));
		end if;	
		fac:=Factorization(d);
		K`FactorizedDiscriminant:=fac;
	else 	
		fac:=	K`FactorizedDiscriminant;
		
	end if;
	primelist:=[];
	for i in fac do
			Append(~primelist,i[1]);
	end for;
	DegList:=[];
	IndexExpo:=0;
	Indexprimes:=[];

for p in primelist do
	Montes(K,p);
	DegList:=DegList cat [Degree(i):i in K`PrimeIdeals[p]];
    IndexExpo:=IndexExpo+K`LocalIndex[p]*Degree(p);
    if K`LocalIndex[p] gt 0 then
    	Append(~Indexprimes,p);
    end if;
end for;
K`Index:=Indexprimes;
KK:=InfinityRepresentation(K);
KK`Index:=[t];
return IndexExpo,DegList;

else
DegList:=[];
IndexExpo:=0;


for p in K`Index do
	Montes(K,p);
	DegList:=DegList cat [Degree(i):i in K`PrimeIdeals[p]];
    IndexExpo:=IndexExpo+K`LocalIndex[p]*Degree(p);
end for;
return IndexExpo,DegList;
end if;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic pBasisRed(I::Rec,p::RngUPolElt:Reduced:=false)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set
true an p-orthonormal basis of I}

//Initialization
Factorization(~I);
F:=I`Parent;	n:=Degree(F);
Primes:=F`PrimeIdeals[p];	s:=#Primes;
kt:=PolynomialRing(ConstantField(F));	kx<x>:=PolynomialRing(kt); K:=BaseField(F);
Montes(F,p);


if Reduced eq true and forall{i:i in F`PrimeIdeals[p]|i`e  eq 1 } then
	B,_,_,_,_,shiftval:=pBasis(I,p);
	return B,[0:i in [1..n]],0,0,0,shiftval;
end if;

//Initializing Exponentes of p-part of ideal
Expos:=[0:i in [1..#F`PrimeIdeals[p]]];
for i in I`Factorization do
	if i[1] eq p then 	
		Expos[i[2]]:=i[3];	
	end if;
end for;


//Ziehe groessten p(t)^a*O_F aus I heraus und speicher p(t)^a 
killexpo:=0;
if forall{i:i in [1..s]|Expos[i] gt 0 } then
	killexpo:=Minimum([Floor(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
if forall{i:i in [1..s]|Expos[i] lt 0 } then
	killexpo:=Maximum([Ceiling(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;

//Determination of Okutsu bases: 
if not IsDefined(F`localbasedata,p) then
	LocalBases:=[];
	VallMatrix:=[];
	PhiValMatrix:=[];
	for i in [1..s] do 
		r:=#Primes[i]`Type;		e_P:=Primes[i]`e;	n_P:=e_P*Primes[i]`f;    a_P:=Expos[i];         
		Phis:= [Primes[i]`Type[j]`Phi:j in [1..r]];
		PhiDeg:=[Degree(j):j in Phis];
		PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
		Phis:=[x] cat Phis;
		BasisVals:=[* *];
		PhiVals:=[* *];
		for l in [1..s] do 
			BasisValstmp:=[Rationals()!0:i in [1..n_P]];
			PhiValstmp:=[PhiValuation(F,p,[i,o],l):o in [0..#Primes[i]`Type] ];
			
			for k in [1..n_P-1] do
				BasisValstmp[k+1]:=&+[PhiExpos[k,ll]*PhiValstmp[ll]:ll in [1..#PhiExpos[k] ]];
			end for;
			Append(~BasisVals,BasisValstmp);
			Append(~PhiVals,PhiValstmp);
		end for;
		Append(~PhiValMatrix,PhiVals);
		Append(~VallMatrix,BasisVals);
		localBasis:=[kx!1] cat [ kx!&*[Phis[j]^PhiExpos[k][j]:j in [1..#Phis-1]]:k in [1..n_P-1]];
		Append(~LocalBases,localBasis);
	end for;

	F`localbasedata[p]:=[*LocalBases,VallMatrix,PhiValMatrix*];
else
	LocalBases:=F`localbasedata[p][1];
	VallMatrix:=F`localbasedata[p][2];
	PhiValMatrix:=F`localbasedata[p][3];
end if;

FacIndex,Facprecision,DenExpos,NormValues:=Multipliers2(F,p,Expos,PhiValMatrix,VallMatrix,Reduced);
alpha:=Maximum([Ceiling(Expos[j]/Primes[j]`e):j in [1..s]])+1;
Base:=[];
groupedNormValues:=NormValues;
NormValues:=&cat NormValues;	_,Possi:=Maximum(NormValues);
constminus:=Minimum([-Expos[j]/Primes[j]`e:j in [1..#Expos]]);
modalphas:=[[Maximum([Ceiling(ll-constminus),0])+1:ll in j]:j in groupedNormValues];
Multis,Indices,exportexpos:=ComputMultisShort(F,p,FacIndex,Facprecision,PhiValMatrix,modalphas);
pmodExpos:=ProdList([Maximum([Ceiling(j),0])+1:j in NormValues],p);
pevModExp:=exportexpos[Possi];
_,maxindex:=Maximum(NormValues);

lauf:=1;
for i in [1..#LocalBases] do
	for j in [1..#LocalBases[i]] do
		Append(~Base,Evaluate(F,(LocalBases[i,j]* Multis[i])) mod exportexpos[lauf]);//pmodExpos[lauf]
		lauf:=lauf+1;	
	end for;
end for;
DenExpos:=&cat DenExpos;
modalphasList:=&cat modalphas;
for i in [1..n] do
	TMP:=Parent([p])!Eltseq(Base[i]);
	Base[i]:=F![TMP[j] mod exportexpos[i]: j in [1..#TMP]];
end for;
if Reduced eq true then
	Normes:=[];
	for i in [1..s] do
		if not FacIndex[i] eq [] then
			addtmp:=&+[PhiValMatrix[l,i,#PhiValMatrix[l,i]]:l in FacIndex[i]];
		else
			addtmp:=0;
		end if;
		for j in [1..#groupedNormValues[i]] do	
			Append(~Normes,groupedNormValues[i,j]+addtmp );	
		end for;
	end for;	
	return [Base[i]/F!p^DenExpos[i]:i in [1..n]],[-i-Ceiling(-i):i in Normes],Multis,Base,p,killexpo,Maximum(DenExpos);
end if;

//////////////Transforming into HNF////////////////////

denexxo:=Sort(DenExpos);
zeta:=-Maximum(DenExpos);
DenExpos:=[-i-zeta:i in DenExpos];
PreBase:=Reverse(Sort([p^DenExpos[i]*Base[i]:i in [1..#Base]],func<x, y | Deg(x) - Deg(y)>));
MatList:=[];
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([p])!Eltseq(PreBase[j])));
end for;
if Reduced eq false then
		H:=HermiteForm(Matrix(MatList));
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=pevExp;
		for j in [i+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;
	Denoms:=[-(i+zeta):i in Denoms];
	H:=HermiteForm(Matrix(MatList));
	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^zeta:i in [1..Degree(F)]]);
else
	Posi:=Signature(NormValues,[i`e:i in F`PrimeIdeals[p]]);
// HNF fuer reduzierte Basis
	for j in [1..#Posi] do
		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;
	end for;
// Normalisieren der Basis
	for i in [1..n] do
		nN:=exists(ind){ y : y in [1..n] | not MatList[i,y] eq 0};
		exp:=Valuation(MatList[i,ind],p);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,ind]/pevExp),pevModExp);
		MatList[i,ind]:=pevExp;
		for j in [ind+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;	

// HNF fuer reduzierte Basis zum 2.
	for j in [1..#Posi] do

		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;		
	end for;
	Base:=Sort(Reverse([F!  Parent([p])!Reverse(Eltseq(MatList[i])) *K!p^zeta:i in [1..Degree(F)]]),func<x, y | Deg(x) - Deg(y)>);
	return Base,[],0,kt!1,p,killexpo;
end if;


if p in F`Index and assigned F`IndexBases and not IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then
	F`IndexBases[p]:=[*Base,Sort(Denoms),pevModExp,alpha,p,killexpo*];
end if;

return Base,Sort(Denoms),pevModExp,alpha,p,killexpo;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic pBasis(I::Rec,p::RngUPolElt:Red:=false,MaxMin:=true)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set true an p-orthonormal basis of I}

/*if MaxMin then

	if Red then
		return pBasisTriangular(I,p);
	else
		return pIdealBasis(I,p);
	end if;
else
	return pBasisMultiplier(I,p:Reduced:=Red);
end if;*/
	return pBasisMultiplier(I,p:Reduced:=Red);

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic pBasisMultiplier(I::Rec,p::RngUPolElt:Reduced:=false)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set true an p-orthonormal basis of I}

//Initialization
Factorization(~I);
F:=I`Parent;	n:=Degree(F);
Primes:=F`PrimeIdeals[p];	s:=#Primes;
kt:=PolynomialRing(ConstantField(F));	kx<x>:=PolynomialRing(kt); K:=BaseField(F);
Montes(F,p);


if Reduced eq true and &*[i`e:i in F`PrimeIdeals[p]] eq 1 then
	Reduced:=false;
end if;

if Reduced eq true and forall{i:i in F`PrimeIdeals[p]|i`e  eq 1 } then
	Reduced:=false;
end if;

//Initializing Exponentes of p-part of ideal
Expos:=[0:i in [1..#F`PrimeIdeals[p]]];
for i in I`Factorization do
	if i[1] eq p then 	
		Expos[i[2]]:=i[3];	
	end if;
end for;


//Ziehe groessten p(t)^a*O_F aus I heraus und speicher p(t)^a 
killexpo:=0;
if forall{i:i in [1..s]|Expos[i] gt 0 } then
	killexpo:=Minimum([Floor(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
if forall{i:i in [1..s]|Expos[i] lt 0 } then
	killexpo:=Maximum([Ceiling(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
//Wenn 
if IsDefined(F`LocalIndex,p) and Expos eq [0:i in [1..s]] then
	if F`LocalIndex[p] eq 0 then

		return [F.1^i:i in [0..n-1]],[0:i in [0..n-1]],kt!1,1,p,killexpo ;
	end if;
end if;

if assigned F`Index then
	if p in F`Index and assigned F`IndexBases and IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then
		return F`IndexBases[p,1],F`IndexBases[p,2],F`IndexBases[p,3],F`IndexBases[p,4],F`IndexBases[p,5],killexpo;
	end if;
end if;
//Determination of Okutsu bases: 
if not IsDefined(F`localbasedata,p) then
	LocalBases:=[];
	VallMatrix:=[];
	PhiValMatrix:=[];
	for i in [1..s] do 
		r:=#Primes[i]`Type;		e_P:=Primes[i]`e;	n_P:=e_P*Primes[i]`f;    a_P:=Expos[i];         
		Phis:= [Primes[i]`Type[j]`Phi:j in [1..r]];
		PhiDeg:=[Degree(j):j in Phis];
		PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
		Phis:=[x] cat Phis;
		BasisVals:=[* *];
		PhiVals:=[* *];
		for l in [1..s] do 
			BasisValstmp:=[Rationals()!0:i in [1..n_P]];
			PhiValstmp:=[PhiValuation(F,p,[i,o],l):o in [0..#Primes[i]`Type] ];
			for k in [1..n_P-1] do
				BasisValstmp[k+1]:=&+[PhiExpos[k,ll]*PhiValstmp[ll]:ll in [1..#PhiExpos[k] ]];
			end for;
			Append(~BasisVals,BasisValstmp);
			Append(~PhiVals,PhiValstmp);
		end for;
		Append(~PhiValMatrix,PhiVals);
		Append(~VallMatrix,BasisVals);
		localBasis:=[kx!1] cat [ kx!&*[Phis[j]^PhiExpos[k][j]:j in [1..#Phis-1]]:k in [1..n_P-1]];
		Append(~LocalBases,localBasis);
	end for;

	F`localbasedata[p]:=[*LocalBases,VallMatrix,PhiValMatrix*];
else
	LocalBases:=F`localbasedata[p][1];
	VallMatrix:=F`localbasedata[p][2];
	PhiValMatrix:=F`localbasedata[p][3];
end if;

FacIndex,Facprecision,DenExpos,NormValues:=Multipliers2(F,p,Expos,PhiValMatrix,VallMatrix,Reduced);

alpha:=Maximum([Ceiling(Expos[j]/Primes[j]`e):j in [1..s]])+1;
Base:=[];
groupedNormValues:=NormValues;
NormValues:=&cat NormValues;

_,Possi:=Maximum(NormValues);
constminus:=Minimum([-Expos[j]/Primes[j]`e:j in [1..#Expos]]);
modalphas:=[[Maximum([Ceiling(ll-constminus),0])+1:ll in j]:j in groupedNormValues];
Multis,Indices,exportexpos:=ComputMultisShort(F,p,FacIndex,Facprecision,PhiValMatrix,modalphas);
pmodExpos:=ProdList([Maximum([Ceiling(j),0])+1:j in NormValues],p);
pevModExp:=exportexpos[Possi];
_,maxindex:=Maximum(NormValues);

lauf:=1;
for i in [1..#LocalBases] do
	for j in [1..#LocalBases[i]] do
		Append(~Base,Evaluate(F,(LocalBases[i,j]* Multis[i])) mod exportexpos[lauf]);//pmodExpos[lauf]
		lauf:=lauf+1;	
	end for;
end for;

DenExpos:=&cat DenExpos;
modalphasList:=&cat modalphas;
for i in [1..n] do
	TMP:=Parent([p])!Eltseq(Base[i]);
	Base[i]:=F![TMP[j] mod exportexpos[i]: j in [1..#TMP]];
end for;

//////////////Transforming into HNF////////////////////
denexxo:=Sort(DenExpos);
zeta:=-Maximum(DenExpos);
DenExpos:=[-i-zeta:i in DenExpos];
PreBase:=Reverse(Sort([p^DenExpos[i]*Base[i]:i in [1..#Base]],func<x, y | Deg(x) - Deg(y)>));
MatList:=[];
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([p])!Eltseq(PreBase[j])));
end for;
if Reduced eq false then
	H:=HermiteForm(Matrix(MatList));
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=pevExp;
		for j in [i+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;
	Denoms:=[-(i+zeta):i in Denoms];
	H:=HermiteForm(Matrix(MatList));
	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^zeta:i in [1..Degree(F)]]);
else
	Posi:=Signature(NormValues,[i`e:i in F`PrimeIdeals[p]]);
// HNF fuer reduzierte Basis
	for j in [1..#Posi] do
		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;
	end for;
// Normalisieren der Basis
	for i in [1..n] do
		nN:=exists(ind){ y : y in [1..n] | not MatList[i,y] eq 0};
		exp:=Valuation(MatList[i,ind],p);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,ind]/pevExp),pevModExp);
		MatList[i,ind]:=pevExp;
		for j in [ind+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;	

// HNF fuer reduzierte Basis zum 2.
	for j in [1..#Posi] do

		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;		
	end for;
	Base:=Sort(Reverse([F!  Parent([p])!Reverse(Eltseq(MatList[i])) *K!p^zeta:i in [1..Degree(F)]]),func<x, y | Deg(x) - Deg(y)>);
	return Base,[],0,kt!1,p,killexpo;
end if;

if assigned F`Index then
	if p in F`Index and assigned F`IndexBases and not IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then
		F`IndexBases[p]:=[*Base,Sort(Denoms),pevModExp,alpha,p,killexpo*];
	end if;
end if;
return Base,Sort(Denoms),pevModExp,alpha,p,killexpo;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Multipliers2(F::FldFun,p::RngUPolElt,Expos:: SeqEnum, PhiVals::SeqEnum,BasisVals::SeqEnum,Reduced::BoolElt)->SeqEnum
{Computes computes Multiplier}
//print"BasisVals:",BasisVals;print"PhiVals:",PhiVals;
s:=#PhiVals;
FactorIndex:=[Remove([1..s],i):i in [1..s]];
BasisNorm:=[[]:i in [1..s]];

//Berechnung der Norm der Basis Elemente
for l in [1..s] do
	
	for i in [1..s] do 
		if #FactorIndex[l] gt 0 then
		phiadjustment:=&+[PhiVals[j,i,#PhiVals[j,i]]:j in FactorIndex[l]];//- Expos[i]/F`PrimeIdeals[p,i]`e;
		BasisNorm[l,i]:=[BasisVals[l,i,j]- Expos[i]/F`PrimeIdeals[p,i]`e +phiadjustment  :j  in [1..#BasisVals[l,1]]];
		end if;
	end for;
end for;

PrecisionIndex:=[[]:i in [1..s]];

for l in [1..s] do
	
	for i in Remove([1..s],l) do
			phival_i_l:=PhiVals[i,l,#PhiVals[i,l]]; phival_i_i:=PhiVals[i,i,#PhiVals[i,i]];
			ttmmpp:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,i,rr]-phival_i_i):rr in [1..#BasisVals[l,1]]];
			m_0:=Maximum(ttmmpp);
			val1:=m_0 ge 0 and i lt l; val2:=m_0 gt 0 and i gt l;
			if Reduced then val2:=m_0 ge 0; end if;
			if val1 or val2 then 
				Append(~PrecisionIndex[l],i);
				
			else	
				LL:=Remove([1..s],l);				
				CheckList:=[1];
				for j in Remove(LL,Position(LL,i)) do	// hier berechne ich was doppelt
					ttmmpp2:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,j,rr]-PhiVals[j,i,#PhiVals[j,i]]):rr in [1..#BasisVals[l,1]]];
					m:=Maximum(ttmmpp2);	
					if  j lt l or Reduced then			
						if  m ge 0 then							
							Append(~CheckList,0);							
						end if;
					else
						if  m gt 0 then
							Append(~CheckList,0);						
						end if;				
					end if;			
				end for;				
			if &*CheckList eq 1 then					
				FactorIndex[l]:=Remove(FactorIndex[l],Position(FactorIndex[l],i));
				for z in [1..s] do
					NormAdjusment:=PhiVals[i,z,#PhiVals[i,z]];
					for y in [1..#BasisNorm[l,1]] do						
						BasisNorm[l,z,y]:=BasisNorm[l,z,y]-NormAdjusment;						
					end for;					
				end for;
			end if;			
			end if;
	end for;
end for;

//Nachbesserungen:
PrecisionIndex,FactorIndex:=MultiplierH([*F,p*],Expos, PhiVals,BasisNorm,FactorIndex,Reduced);

Precision:=[[0:j in [1..#FactorIndex[i]]]:i in [1..s]];

//Berechnung der SFL-Werte
for l in [1..s] do 

	if FactorIndex[l] ne [] then

		Adj1:=&+[ PhiVals[j,l,#PhiVals[j,l]] :j in FactorIndex[l] ]- Expos[l]/F`PrimeIdeals[p,l]`e;
		LSList:=[BasisVals[l,l,#BasisVals[l,1]]+ Adj1:rr in [1..#BasisVals[l,1]]];
		for i in  FactorIndex[l] do 
			RSList:=[];
			for mm in [1..#BasisVals[l,1]] do
				iPosition:=Position(FactorIndex[l],i);
				phiindices:=Remove(FactorIndex[l],iPosition);	

				if #phiindices gt 0 then 
			
					Adj2:=&+[ PhiVals[j,i,#PhiVals[j,i]] :j in phiindices ]- Expos[i]/F`PrimeIdeals[p,i]`e;
				else
					Adj2:=- Expos[i]/F`PrimeIdeals[p,i]`e;
				end if;	
				Append(~RSList,BasisVals[l,i,mm]+ Adj2);
			end for;			
			q:=Maximum([LSList[i]-RSList[i]:i in [1..#LSList]]);		
			prec:=Ceiling(q*F`PrimeIdeals[p,i]`e);
			Boolval:=i lt l;
			if Reduced then Boolval:=true; end if;
			if Boolval and q ge 0 then 
				Precision[l,Position(FactorIndex[l],i)]:=prec + F`PrimeIdeals[p,i]`e;			
			end if;			
			if l lt i and q gt 0  then
				Precision[l,Position(FactorIndex[l],i)]:=prec ;							
			end if;			
		end for; 	
	end if;	
end for;

DenExp:=[];
NormVals:=[];

//Berechnung der Norm der Basiselemente
for l in [1..s] do

	DenExptmp:=[];
	NormValstmp:=[];
	for i in [1..#BasisVals[l,1]] do					
		prec:=BasisVals[l,l,i]-Expos[l]/F`PrimeIdeals[p,l]`e;		
		if FactorIndex[l] ne [] then		
		Adj:=&+[PhiVals[ jj,l ,#PhiVals[jj,l] ] :jj in FactorIndex[l]];						
		Append(~DenExptmp, Floor(prec+Adj));
		Append(~NormValstmp, prec+Adj);
	else	
		Append(~DenExptmp, Floor(prec));
		Append(~NormValstmp, prec);		
	end if;	
	end for;
	
	Append(~DenExp,DenExptmp);
	Append(~NormVals,NormValstmp);
end for;		
return FactorIndex,Precision,DenExp,NormVals,BasisNorm,PhiVals;
end intrinsic;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ReductionAlgorithm(T::AlgMatElt:InA:=false)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
NumberRedSteps:=0;

lc:=LCM([Denominator(i):i in Eltseq(T)]);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n:=Ncols(T);m:=Nrows(T);
T:=Parent(ZeroMatrix(kt,n,n))!(lc*T);

s:=1;

if m eq 1 then return T,Maximum([Deg(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p:=[];
Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);

while s lt m do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..m] do
			if not T[i,j] eq 0 and Degree(T[i,j]) eq VectorNorm[i] then			
				M[i,j]:=LeadingCoefficient(T[i,j]);				
			end if; 				
		end for;
	end for;
	Mprime,P:=EchelonForm(M);
	s:=Rank(Mprime);
	NumberRedSteps:=NumberRedSteps+m-s;

	if s lt m then
			//Transform P in a shape to read out all relations
		Su:=SubmatrixRange(P,s+1,1,n,n);
		P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
		for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			for i in [1..u-1] do
				if not P[j,i] eq 0 then								
				AddRow(~T,P[j,i]/P[j,u]*t^(VectorNorm[u]-VectorNorm[i]),i,u);
				end if;
			end for;
			VectorNorm[u]:=Maximum([Degree(l):l in ElementToSequence(T[u])]);
		end for;
		p:=[];
		Sort(~VectorNorm,~p);
		T:=Matrix([T[i]:i in Eltseq(p)]);
	end if;
end while;	
print"NumberRedSteps",NumberRedSteps;
if InA then 
	return lc,T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
else
	return (1/K!lc)*T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic ReductionAlgorithmSAT(T::ModMatFldElt:InA:=false)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
NumberRedSteps:=0;

lc:=LCM([Denominator(i):i in Eltseq(T)]);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n:=Ncols(T);m:=Nrows(T);
T:=Parent(ZeroMatrix(kt,m,n))!(lc*T);

if m eq 1 then return T,Maximum([Deg(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p:=[];
Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);

while Maximum(VectorNorm) - Degree(lc) gt 0  do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..n] do
			if not T[i,j] eq 0 and Degree(T[i,j]) eq VectorNorm[i] then			
				M[i,j]:=LeadingCoefficient(T[i,j]);				
			end if; 				
		end for;
	end for;
	Mprime,P:=EchelonForm(M);
	s:=Rank(Mprime);
	NumberRedSteps:=NumberRedSteps+m-s;

	if s lt m then
			//Transform P in a shape to read out all relations
		Su:=SubmatrixRange(P,s+1,1,m,m);
		P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
		for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			for i in [1..u-1] do
				if not P[j,i] eq 0 then	
				AddRow(~T,P[j,i]/P[j,u]*t^(VectorNorm[u]-VectorNorm[i]),i,u);
				end if;
			end for;
			VectorNorm[u]:=Maximum([Degree(l):l in ElementToSequence(T[u])]);
		end for;
		p:=[];
		Sort(~VectorNorm,~p);
		T:=Matrix([T[i]:i in Eltseq(p)]);
	end if;
end while;	
if InA then 
	return lc,T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
else
	return K!(1/lc)*Parent(ZeroMatrix(K,m,n))!T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic ReductionAlgorithm(T::AlgMatElt, Values::SeqEnum)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}

Vals:=SetToSequence(Set(Values));
lc,T,VectorNorm,NumberRedSteps:=ReductionAlgorithm(T:InA:=true);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);

if #Vals eq 1 then 
	return (1/K!lc)*T,VectorNorm,NumberRedSteps;
end if;

l:=1;
VectorNorm:=[Norm(i,Values):i in RowSequence(T)];
p:=[];Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);
while l le #Vals do
	ColumnIndex:=[ y : y in  [1..#Values] | Values[y] eq Vals[l]];
	RowIndex:=[ y : y in  [1..#VectorNorm] | (VectorNorm[y]-Ceiling(VectorNorm[y])) eq Vals[l]];

	m:=#RowIndex;	n:=#ColumnIndex;
	M:=ZeroMatrix(k,m,n);

	if m gt 1 then
	
		for i in [1..m] do
			for j in [1..n] do
				if not T[RowIndex[i],ColumnIndex[j]] eq 0 
					and Degree(T[RowIndex[i],ColumnIndex[j]])+Vals[l] eq VectorNorm[RowIndex[i]] then			
					M[i,j]:=LeadingCoefficient(T[RowIndex[i],ColumnIndex[j]]);				
				end if; 				
			end for;
		end for;
		Mprime,P:=EchelonForm(M);
		s:=Rank(Mprime);
		if s eq m then 
			if m lt n and not Vals[l] in [Vals[i]:i in [l+1..#Vals]] then 
				Append(~Vals,Vals[l]);
			end if;	
						
		else
			NumberRedSteps:=NumberRedSteps+m-s;
			Su:=SubmatrixRange(P,s+1,1,m,m);
			P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
			for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			jj:=RowIndex[u];
				for i in [1..u-1] do
					
					if not P[j,i] eq 0 then
						ii:=RowIndex[i];
						AddRow(~T,P[j,i]/P[j,u]*t^(Ceiling(VectorNorm[jj])-Ceiling(VectorNorm[ii])),ii,jj);
					end if;	
				end for;

				VectorNorm[jj]:=Norm(ElementToSequence(T[jj]),Values);
			
				if not VectorNorm[jj]-Ceiling(VectorNorm[jj]) in [Vals[i]:i in [l+1..#Vals]] then 
					Append(~Vals,VectorNorm[jj]-Ceiling(VectorNorm[jj]));
				end if;				

			end for;
			p:=[];
			Sort(~VectorNorm,~p);
			T:=Matrix([T[i]:i in Eltseq(p)]);
		end if;

	end if;
	l:=l+1;
end while;	

return  (1/K!lc)*T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;

end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



intrinsic SIdealBase(I::Rec, primelist::SeqEnum:Maximal:=false)->SeqEnum
    {Compute a local integral basis of I for the given set of primes.}
    K:=I`Parent;
    if primelist eq [] then return [K.1^i:i in [0..Degree(K)-1]]; end if;
    n:=Degree(I`Parent);
    Numlist:=[];    Denlist:=[];    DenlistCRT:=[];    ZetaList:=[];    faclist:=[];
    Factorization(~I);
    Rt:=Parent(primelist[1]);
	R<x>:=PolynomialRing(Rt);

for p in primelist do
	Montes(I`Parent, p );
        // Exponents of the prime ideals

	pBase, pVals, pmod, alphap,factm,killexp:= pBasis(I, p); 
	if Maximal eq true and not IsDefined(K`IndexBases,p) then 
		K`IndexBases[p]:=[*pBase,pVals, pmod, alphap,factm,killexp*]; 	
	end if;    
	if 	#primelist eq 1 then return pBase,BaseField(K)!factm^killexp; end if;
	Append(~faclist,BaseField(K)!factm^killexp);
	pBase:=Reverse(pBase);	pVals:=Reverse(pVals);
	NumListe:=[];			zeta:=-Maximum(pVals);
	Append(~ZetaList,BaseField(K)!p^zeta);	// kann man verbessern
	for i in [1..n] do
  		if pVals[i] le 0 then // sollte nicht lt reichen!
     		CList:=Reverse(Eltseq(pBase[i]*BaseField(K)!p^pVals[i]));
        	Append(~NumListe, [Rt!CList[ll]:ll in [i..n]] );
        else
        	CList:=Reverse(Eltseq(Numerator(pBase[i])) );
        	Append(~NumListe, [Rt!CList[ll]:ll in [i..n]]);
	  	end if;
    end for;
    Append(~Numlist,NumListe);    Append(~Denlist,[BaseField(K)!p^(-v-zeta) : v in pVals]);
    tmpList:=[];
    for i in pVals do
        ex:=Maximum([i+1,0])+Maximum([alphap,0]);
        Append(~tmpList,p^ex);           			
	end for;
    Append(~DenlistCRT, tmpList);
end for;
MatList:=[];  

for i in [1..n] do
    NewCoeff:=[];
   	for m in [1..n-i+1] do
   		CoeffList:=[Numlist[j,i,m]: j in [1..#primelist]];	CRTList:=[DenlistCRT[j,i]: j in [1..#primelist]]; 
	    Append(~NewCoeff,CRT(CoeffList,CRTList));		
    end for;
    fac:=Parent(primelist[1])!&*[Denlist[jj,i]:jj in [1..#primelist]];
    Append(~MatList,[l*fac:l in NewCoeff]);	
end for;

H:=HermiteForm(UpperTriangularMatrix(&cat MatList));
ZETA:=&*ZetaList; 
Base:=Reverse([K!Reverse([m :m in Eltseq(H[i])])*ZETA: i in [1..n]]);	
return Base,&*faclist;
end intrinsic;

//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic RationalRadical(I::Rec)->SeqEnum
{Compute the rational prime numbers dividing the norm of the ideal I.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "Argument is neither an IdealRecord nor a PrimeIdealRecord";
require not IsZero(I): "Argument must be a non-zero ideal.";

return SetToSequence(Set([x[1]: x in Factorization(I)]));
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic RandomDivisorClass(F::FldFun)->Rec
{Produces a representative of a divisor class of degree 0.}
require IsGlobal(F): "Function field is not global";

g:=GENUS(F);
Fq:=ConstantField(F);	q:=#Fq;		A:=DivisorOfDegree1(F);
d:=Random([1..Maximum([g,1])]);
if d eq 1 then 
	d_tmp:=Random([0..q]);
	if d_tmp eq q then 
		P:=Random(PlacesAtInfinity(F));
		return P-Degree(P)*A;
	else	
		p:=PolynomialRing(Fq).1-Fq!d_tmp;
		Montes(F,p);
		P:=Divisor(Random(F`PrimeIdeals[p]));
		return P-Degree(P)*A;
	end if;	
else
	p:=RandomPrimePolynomial(PolynomialRing(Fq),d);
	Montes(F,p);
	P:=Divisor(Random(F`PrimeIdeals[p]));
	return P-Degree(P)*A;
end if;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic RandomDivisor(F::FldFun,l::RngIntElt)->Rec
{Produces a divisor.}


a := Random(F,l);
while a eq 0 do

	a := Random(F,l);	

end while;
S1 := Support(Divisor(a));
while  #S1 eq 0 do
	a := Random(F,l);
	S1 := Support(Divisor(a));
end while;

g := GENUS(F);
D := &+[Random([-g..g])*Divisor(i):i in S1];

return D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic RandomDivisor_effective_multi(F::FldFun,l::RngIntElt)->Rec
{Produces a divisor.}

Fpt := PolynomialRing(ConstantField(F));
D := Divisor(F!1);
idealss := [];
g := GENUS(F);
for i in [1..l] do

	p := RandomPrimePolynomial(Fpt,Random([1..Min([6,g])]));
	Montes(F,p);
	I := &*[P^Random([-g..-1]): P in F`PrimeIdeals[p]];
	Append(~idealss,I);

end for;
I := &*idealss;
//I_inf := &*[P^Random([-g..-1]): P in PrimesAtInfinity(F)];
D_0 := Divisor(I);
D_inf := Divisor(F!1);//Divisor(&*[P^Random([-g..-1]):P in PrimesAtInfinity(F)]);


return D_0+D_inf;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic RandomDivisor_neg(F::FldFun,l::RngIntElt)->Rec
{Produces a divisor.}


a := Random(F,l);
S1 := Support(Divisor(a));
while  #S1 eq 0 do
	a := Random(F,l);
	S1 := Support(Divisor(a));
end while;

g := GENUS(F);
D := &+[Random([-g..0])*Divisor(i):i in S1];

return D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic PhiExpo(m::RngIntElt,DegList::SeqEnum)->SeqEnum
{Compute mi/m_i-1 representation of an integer m}
L:=[];
DegList:=[1] cat DegList;
BoundList:=[Integers()!(DegList[i]/DegList[i-1]):i in [2..#DegList]];
for i in [1..#BoundList] do
	Append(~L,Integers()!(m mod BoundList[i]));
	m:=m div BoundList[i];
end for;

return L;

end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PhiValuation(F::FldFun,p::RngUPolElt,IndexPhi:: SeqEnum, IndexPrime::RngIntElt)->RngIntElt
{Computes the valuation of Phi at Prime}

P:=IndexPhi[1];
i:=IndexPhi[2];
if i eq 0 then 	
	if Degree(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi) gt 1 then
		return 0;		
	else
		if F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi eq Parent(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi).1 then
			return $$(F,p,[P,1],IndexPrime);			
		else	
			tmp:=Minimum([Valuation(Eltseq(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi)[1],p),F`PrimeIdeals[p,IndexPrime]`Type[1]`slope]);
			return tmp;
		end if;		
	end if;	

end if;
Q:=IndexPrime;
t1:=F`PrimeIdeals[p,P]`Type;
if P eq Q then
	return (t1[i]`V+Abs(t1[i]`slope))/t1[i]`prode;
end if;
t2:=F`PrimeIdeals[p,Q]`Type;
IndexOfCoincidence(~t1,~t2,~ioc);

if ioc eq 0 then 
	return 0;
else
	Ref1:=Append(t1[ioc]`Refinements,[* t1[ioc]`Phi,t1[ioc]`slope *]);
	Ref2:=Append(t2[ioc]`Refinements,[* t2[ioc]`Phi,t2[ioc]`slope *]);
	minlength:=Min(#Ref1,#Ref2);
	ii:=2;
	while ii le minlength and Ref1[ii,1] eq Ref2[ii,1] do 
	    ii+:=1;    
	end while;
	hiddenslope1:=Ref1[ii-1,2];
	hiddenslope2:=Ref2[ii-1,2];
	minslope:=Min([hiddenslope1,hiddenslope2]);
	entry:=(t1[ioc]`V+minslope)/t1[ioc]`prode;

	if i lt ioc then 
		return (t1[i]`V+Abs(t1[i]`slope))/t1[i]`prode;	
	end if;
	
	if i eq ioc then 	
		if Ref1[ii-1,1] eq t1[ioc]`Phi then 
			return (t1[ioc]`V+hiddenslope2)/t1[ioc]`prode;		
		else
			return entry;	
	
		end if;
	else 
		return entry*Degree(t1[i]`Phi)/Degree(t1[ioc]`Phi);
	end if;	
end if;	
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ComputMultisShort(F::FldFun,p::RngUPolElt,FacIndex:: SeqEnum, Facprecision::SeqEnum,PhiVals::SeqEnum,modalphas::SeqEnum)->SeqEnum
{Determines Multipliers}

//print"FacIndex",FacIndex,Facprecision;
s:=#FacIndex;
ModExponents:=[];
ModExpList:=[];
for i in [1..s] do

	if Facprecision[i] eq [] then
		Append(~ModExponents,1);
	else
		for l in [1..#FacIndex[i]] do
		phivalues:=[Facprecision[i,l]/F`PrimeIdeals[p,FacIndex[i,l]]`e] cat [PhiVals[l,j,#PhiVals[l,1]]: j in Remove([1..s],l)];
		Append(~ModExponents,Ceiling(Maximum([0] cat phivalues))+1);
		end for;
		tmpl:=[];
			
	end if;
	Append(~ModExpList,ModExponents);
	ModExponents:=[];
end for;
LengthModExp:=[#j:j in ModExpList];
factorModList,EndExpos,exportexpos:=Subsec(ModExpList,p,modalphas);

kx<x>:=PolynomialRing(PolynomialRing(ConstantField(F)));
Multis:=[[kx!1]:i in [1..s]];
MultiIndex:=[[]:i in [1..s]];
for i in [1..s] do
	SFLList:=[-1:i in [1..s]];
	for j in [1..s] do	
		if i in FacIndex[j] then
			SFLList[j]:=Facprecision[j,Position(FacIndex[j],i)];		
		end if;	
	end for;
	SortSFLList:=Sort(SFLList);
	Bijec:=Sort(SFLList,SortSFLList);
	tmp:=0;
	Maxi:=Maximum(SortSFLList);
	if Maxi gt tmp then //kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
			
	
		Slope:=Maxi-F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`V;		
		SFL(~F,~F`PrimeIdeals[p,i],Ceiling(Slope));//SFL(~F`PrimeIdeals[p,i]`Type,Ceiling(Slope));
		tmp:=Maxi; //hier genauso: \\kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
		end if;
	for j in [1..#SortSFLList] do	
		if SortSFLList[j] ge 0 then
			Append(~Multis[Bijec[j]],F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`Phi);
			Append(~MultiIndex[Bijec[j]],i);	
		end if;	
	end for;
end for;
z_kappa:=[];
for ll in [1..#Multis] do
	if #Multis[ll] eq 1 and Multis[ll,1] eq 1 then
		Append(~z_kappa,Multis[ll,1]);
	else		
	Append(~z_kappa,(&*[Multis[ll,mm] mod factorModList[ll,mm-1]:mm in [2..#Multis[ll]]]) mod EndExpos[ll] );//mod EndExpos[mm] 
	end if;
end for;
return z_kappa,MultiIndex,exportexpos;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ProdList(Expos::SeqEnum,p::RngUPolElt)->SeqEnum
{Produces [p^[Expos[i]]:i in [1..#Expos]] in a intelligent way}

Sort(~Expos,~permutation);
Factors:=[];
prod:=1; j:=0;
for i in [1..#Expos] do
	exp:=Expos[i]-j;
	j:=Expos[i];
	prod:=prod*p^exp;
	Append(~Factors,prod);

end for;

return [Factors[j]:j in Eltseq(permutation^-1)];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic MultiplierH(Char::List,Expos:: SeqEnum, PhiVals::SeqEnum,BasisNorm::SeqEnum,FactorIndex::SeqEnum,Reduced::BoolElt)->SeqEnum
{Computes computes Multiplier}
F:=Char[1];	p:=Char[2];
s:=#PhiVals;
//Berechnung der Norm der Basis Elemente
PrecisionIndex:=[[]:i in [1..s]];

for l in [1..s] do	
	for i in Remove([1..s],l) do
			phival_i_l:=PhiVals[i,l,#PhiVals[i,l]]; phival_i_i:=PhiVals[i,i,#PhiVals[i,i]];
			ttmmpp:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,i,rr]-phival_i_i):rr in [1..#BasisNorm[l,1]]];
			m_0:=Maximum(ttmmpp);
			val1:=m_0 ge 0 and i lt l; val2:=m_0 gt 0 and i gt l;
			if Reduced then val2:=m_0 ge 0; end if;
			if val1 or val2 then 
				Append(~PrecisionIndex[l],i);				
			else	
				LL:=Remove([1..s],l);				
				CheckList:=[1];
				for j in Remove(LL,Position(LL,i)) do	// hier berechne ich was doppelt
					ttmmpp2:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,j,rr]-PhiVals[j,i,#PhiVals[j,i]]):rr in [1..#BasisNorm[l,1]]];
					m:=Maximum(ttmmpp2);	
					if  j lt l or Reduced then							
						if  m ge 0 then							
							Append(~CheckList,0);								
						end if;
					else			
						if  m gt 0 then
							Append(~CheckList,0);												
						end if;														
					end if;
				end for;				
			if &*CheckList eq 1 and i in FactorIndex[l] then					
				FactorIndex[l]:=Remove(FactorIndex[l],Position(FactorIndex[l],i));					
				for z in [1..s] do
					NormAdjusment:=PhiVals[i,z,#PhiVals[i,z]];
					for y in [1..#BasisNorm[l,1]] do						
						BasisNorm[l,z,y]:=BasisNorm[l,z,y]-NormAdjusment;						
					end for;					
				end for;
			//Alten Werte auch Ã¼berprÃ¼fen
	
			end if;			
			end if;
	end for;

end for;
Precision:=[[0:j in [1..#FactorIndex[i]]]:i in [1..s]];
return PrecisionIndex,FactorIndex;
end intrinsic;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Subsec(List::SeqEnum,p::RngUPolElt,ExtraList::SeqEnum)->SeqEnum
{Splits Liste into sublists of length Lenght[i]}

Liste:=&cat List;
Liste2:=&cat ExtraList;
Length:=[#i:i in List];
factorList:=ProdList(Liste cat Liste2,p);
exportList:=[factorList[jj]:jj in [#Liste+1..#Liste+#Liste2]];
Liste:=[factorList[jj]:jj in [1..#Liste]];

useherelist:=[];
for l in [1..#ExtraList] do
	Append(~useherelist,exportList[Position(Liste2,Maximum(ExtraList[l]))]);
end for;

if not #Liste eq &+Length  then print"Liste und Length nicht kompatible"; return 0; end if;
	Out:=[];
	LL:=[];j:=1;
	for i in [1..#Liste] do	
		Append(~LL,Liste[i]);
		if i eq &+[Length[ll]:ll in [1..j]] then		
			Append(~Out,LL);
			LL:=[];
			j:=j+1;
		end if;		
	end for;

return Out,useherelist,exportList;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Degree(I::Rec)->RngIntElt
{computes the Degree of a place, prime ideal or a divisor}


if IsPrimeIdealRecord(I) then
	K:=I`Parent;
	if IsFinite(ConstantField(K)) then
		deg:= Integers()!(Degree(I`Type[#I`Type]`Fq)/Degree(ConstantField(K)));
	else
		deg:=Degree(I`Type[#I`Type]`Fq);
	end if;
	return deg;
end if;


if IsIdealRecord(I) then
	K:=I`Parent;
	if #I`Factorization eq 0 then return 0; end if;
	I:=K`PrimeIdeals[I`Factorization[1,1],I`Factorization[1,2]];
	return $$(I);
end if;


/*if IsPlace(I) then
print"asd";
	Ifin:=I`FiniteIdeal^-1;	Iinf:=I`InfiniteIdeal^-1;
	print"Ifin;",Ifin;
	if #Ifin`Factorization eq 0 then
		return $$(Iinf);
	else
		return $$(Ifin);		
	end if;
end if;*/

if IsDivisor(I) then	

	K:=I`FiniteIdeal`Parent;
	L1:=((I`FiniteIdeal)^-1)`Factorization;
	if #L1 gt 0 then
		dfin:=&+[i[3]*$$(K`PrimeIdeals[i[1],i[2]]): i in L1];
	else
		dfin:=0;
	end if;

	L2:=((I`InfiniteIdeal)^-1)`Factorization;
	if #L2 gt 0 then
		PAI:=PrimesAtInfinity(K);

		dinf:=&+[i[3]*$$(PAI[i[2]]): i in L2];
	else
		dinf:=0;
	end if;	

	return dfin+dinf;
end if;	
	

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Dimension(D::Rec)->RngIntElt
{Determines the dimension of the Riemann-Roch space of D}

if assigned D`Basis then return #D`Basis; end if;
F:=D`FiniteIdeal`Parent;
if Degree(D) lt 0 then return 0; end if;
if Degree(D) ge 2*GENUS(F)-1 then
	return Degree(D)+1-GENUS(F);
end if;

if  assigned D`SuccessiveMinima then
	D`ApproximatedSuccessiveMinima := [Ceiling(i):i in D`SuccessiveMinima];
end if;

if not assigned D`SuccessiveMinima and not assigned D`ApproximatedSuccessiveMinima then
	RRSpace2(~D);
end if;
	succMin:=D`ApproximatedSuccessiveMinima;
dim:=0;
for i in succMin do
	if i le 0 then	
		dim:=dim+1-i;	
	end if;
end for;

return dim;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic DivisorOfDegree1(F)->Rec
{}

Fq:=ConstantField(F); A := PolynomialRing(Fq);
require IsFinite(Fq):"Constant field must be finite.";

if assigned F`DivisorOfDegree1 then return F`DivisorOfDegree1; end if;

Pinf:=PrimesAtInfinity(F); 
u := exists(ind){ y : y in Pinf | Degree(y) eq 1};
if u then return Divisor(ind); end if;

Pfin:=F`PrimeIdeals[A.1]; 
u := exists(ind){ y : y in Pfin | Degree(y) eq 1};
if u then return Divisor(ind); end if;


P_0 := Pinf[1];	d_0 :=Degree(P_0);
for i in PrimesAtInfinity(F) do

	P:=i; d:=Degree(P);
	if d eq 1 then return Divisor(P); end if;
	if GCD([d,d_0]) eq 1 then
		_,a,b:=ExtendedGreatestCommonDivisor(d_0,d);
		return a*Divisor(P)+b*Divisor(P_0);
	else
		if d lt d_0 then
			P_0:=P;		d_0:=d;
		end if;
		
	end if;
	
end for;

g,indi:=GENUS(F);

require indi eq 1:"Constant field is not the exact constant field.";


r:=Ceiling(Log(#Fq,2*g));	L:=PrimePolynomials(PolynomialRing(Fq),r);
for i in L do 
	Montes(F,i);
	for j in F`PrimeIdeals[i] do
		
		P:=i; d:=Degree(P);
		if d eq 1 then return Divisor(P); end if;
			if GCD([d,d_0]) eq 1 then
				_,a,b:=ExtendedGreatestCommonDivisor(d_0,d);
			return a*Divisor(P)+b*Divisor(P_0);
		else
			if d lt d_0 then
				P_0:=P;		d_0:=d;
			end if;		
		end if;	
		
	end for;
	
end for;


end intrinsic;
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic Basis(D::Rec:Reduction:=true)->RngIntElt
{Determines the basis of the Riemann-Roch space of D}

if Degree(D) lt 0 then return []; end if;

if not assigned D`RedBasis and not assigned D`SRedBasis then

	if Reduction eq true then
		RRSpace2(~D);
	else	
		RRSpace(~D);	
	end if;

end if;
		succMin:=D`ApproximatedSuccessiveMinima;	


if assigned D`RedBasis then 
	SemiRedBasis:=D`RedBasis;
else
	SemiRedBasis:=D`SRedBasis;
end if;

T:=BaseField(D`FiniteIdeal`Parent).1;
basis:=[];

for i in [1..#succMin] do
	if succMin[i] le 0 then	
		Append(~basis,[SemiRedBasis[i]*T^jj:jj in [ 0..-succMin[i] ] ]);	
	end if;
end for;

return &cat basis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Basis(~D::Rec:Reduction:=true)
{Determines the basis of the Riemann-Roch space of D}

if Degree(D) lt 0 then D`Basis:=[]; return ; end if;

if not assigned D`RedBasis and not assigned D`SRedBasis then

	if Reduction eq true then
		RRSpace2(~D);
	else	
		RRSpace(~D);	
	end if;

end if;
		succMin:=D`ApproximatedSuccessiveMinima;	


if assigned D`RedBasis then 
	SemiRedBasis:=D`RedBasis;
else
	SemiRedBasis:=D`SRedBasis;
end if;

T:=BaseField(D`FiniteIdeal`Parent).1;
basis:=[];

for i in [1..#succMin] do
	if succMin[i] le 0 then	
		Append(~basis,[SemiRedBasis[i]*T^jj:jj in [ 0..-succMin[i] ] ]);	
	end if;
end for;

D`Basis:=&cat basis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ReducedBasis(D::Rec)->SeqEnum
{Determines a reduced basis the lattice corresponding to D}

if not assigned D`RedBasis  then
	RRSpace2(~D:Reduced:=true);
end if;

return D`RedBasis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic SemiReducedBasis(D::Rec)->SeqEnum
{Determines a reduced basis the lattice corresponding to D}

if not assigned D`RedBasis  then
	RRSpace2(~D);
end if;

return D`SRedBasis;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IsPrincipal(D::Rec)->BoolElt
{}

if not Degree(D) eq 0 then return false; end if;

if Dimension(D) gt 0 then 
	return true;
else
	return false;
end if;	
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic PoleDivisor(a::FldFunElt)->FldFun
{Determines the pole divisor of a non zero function z}

require not a eq 0:"Argument must be non zero";

F:=Parent(a); kt:=PolynomialRing(ConstantField(F));

if a in ConstantField(F) then return Divisor(F!1); end if;
den := kt!Denominator(a);	num := Numerator(a);
primes := Factorization(den);

FintePoles:=[];
for i in primes do

	Montes(F,i[1]);
	for j in F`PrimeIdeals[i[1]] do
		tmp:=PValuation(num,j);
		if tmp lt j`e*i[2] then
			Append(~FintePoles,j^(j`e*i[2]-tmp));
		end if;
	end for;

end for;

InfinitePol:=[];

for i in PrimesAtInfinity(F) do

	tmp:=PValuation(num,i);
	if tmp lt -i`e*Degree(den) then
		Append(~InfinitePol,i^(-i`e*Degree(den)-tmp));
	end if;
end for;
print"check2";
if #FintePoles eq 0 or #InfinitePol eq 0 then 
	if #FintePoles eq 0 and #InfinitePol eq 0 then
		D:=	Divisor(F!1);	
	//	if IsReductionOn(F) then DivisorReduction(~D); end if;
		return D;
	end if;

	if #FintePoles eq 0 then
		infinite_ideal := &*InfinitePol;
		D := Divisor(F!1);
		D`InfiniteIdeal := infinite_ideal;
//		D:=D+Divisor(F!1)+&+[Divisor(i):i in InfinitePol];
	else
		D:=&+[Divisor(i):i in FintePoles];
	end if;

	if IsReductionOn(F) then DivisorReduction(~D); end if;

	return -1*D;
end if;

print"check";

D:=&+[Divisor(i):i in FintePoles]+&+[Divisor(i):i in InfinitePol];

if IsReductionOn(F) then
	DivisorReduction(~D);
end if;

return -1*D;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic ZeroDivisor(a::FldFunElt)->FldFun
{Determines the zero divisor of a non zero function z}

require not a eq 0:"Argument must be non zero";

return PoleDivisor(1/a);

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Are_equivalent(D1::Rec,D2::Rec)->BoolElt
{Tests if two divisors belong to the same class modulo principal divisors}

require Degree(D1) eq  Degree(D2):"Arguments must have the same degree";

/*D := D1-D2; DivisorReduction(~D:DivisorClass := false);
print"succ_min",ApproximatedSuccessiveMinima(D);
if Dimension(D) gt 0 then
	return true;
else
return false;
end if;*/

return IsPrincipal(D1-D2);

end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Equal(L1::List ,L2:: List)-> BoolElt
{}
if not #L1 eq #L2 then return false;end if;
for i in [1..#L1] do
	for j in [1..3] do
		if not L1[i,j] eq L2[i,j] then return false; end if;
	end for;
end for;
return true;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic 'eq'(I::Rec ,J:: Rec)-> BoolElt
{True iff the fractional ideals I,J are equal. They are both factored if their factorization is not yet kwown.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I) or IsDivisor(I): "First argument is neither an IdealRecord record nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(J) or IsDivisor(J): "Second argument is neither an IdealRecord record nor a PrimeIdealRecord";

if IsIdealRecord(I) or IsPrimeIdealRecord(I) and IsIdealRecord(J) or IsPrimeIdealRecord(J) then
	if not I`Parent eq J`Parent then return false; end if;
	zi1:=IsZero(I);
	zi2:=IsZero(J);
	if zi1 and zi2 then return true; end if;
	if zi1 or zi2 then return false; end if;

	return Equal(Factorization(I) , Factorization(J));
end if;	

if  $$(I`FiniteIdeal ,  J`FiniteIdeal) and $$(I`InfiniteIdeal , J`InfiniteIdeal) then
	return true;
else
 return false;
end if;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic ElementaryReduction(D::Rec,A::Rec)->Rec
{}

//print"D",D`FactorizationString;
if Height(D) lt 2*GENUS(D`FiniteIdeal`Parent)+1 then return D,0,D`FiniteIdeal`Parent!1;end if; //3*GENUS(D`FiniteIdeal`Parent)
print"ER1";
if Degree(A) eq 0 then  
	return D,0,D`FiniteIdeal`Parent!0;
end if;
F:=D`FiniteIdeal`Parent;	r1:=Ceiling(-Degree(D)/Degree(A));	r2:=Ceiling((GENUS(F)-Degree(D))/Degree(A));
//r1 := Min([r1,r2]); r2 :=Max([r1,r2]);
ElementList:=[];
if r1 lt 1 then
	shift:=-Min([r1,r2])+1;
else	
	shift:=0;	
end if;
print"ER2";
if not r1 eq r2 then
	dimlist:=[];	dimlist[r2+shift]:=1; 	
	dim2:=1;
	
	Dtmp:=D+r1*A;  RRSpace(~Dtmp);	dimlist[1]:=Dimension(Dtmp);
	ElementList[1]:=Dtmp`SRedBasis[1];	
print"ER3";
	if dimlist[1] gt 0 then
print"ER3.1",ElementList[1],Height(Dtmp);
		return Dtmp+Divisor(ElementList[1]),-r1,ElementList[1];
	end if;
	
	D1:=D+(r2-1)*A; RRSpace(~D1);	dim1 := Dimension(D1);	dimlist[(r2-1)+shift]:=1;
print"ER4";	
	if dim1 eq 0 then
		r:=r2; 	D2:=D1+A; RRSpace(~D2); ElementList[r2+shift]:=D2`SRedBasis[1];

	else
		R:=r2-1;
		L:=r1; 
		
		while not dim1 eq 0 or dim2 eq 0 do
			
			r1:=L+Floor((R-L)/2);	r2:=r1+1;	D1:=D+r1*A;		D2:=D1+A;
			if IsDefined(dimlist,r1+shift) then
				dim1:=dimlist[r1+shift];
			else
				RRSpace(~D1);	dim1 := Dimension(D1);	dimlist[r1+shift]:=dim1;
				ElementList[r1+shift]:=D1`SRedBasis[1];
			end if;
print"ER5";			
			if dim1 eq 0 then 
				if IsDefined(dimlist,r2+shift) then
				dim2:=dimlist[r2+shift];
				else
					RRSpace(~D2);	dim2 := Dimension(D2);	dimlist[r2+shift] := dim2;
					ElementList[r2+shift]:=D2`SRedBasis[1];
				end if;
			else
				dim2 := 1;	dimlist[r2+shift] := dim2;
			end if;
			
			if dim1 gt 0 and dim2 gt 0 then				
				R:=r1;
			else
				L:=r2;
			end if;
			
			if dim1 eq 1 and r1 gt 1 then
				if IsDefined(dimlist,r1-1+shift) then
					if dimlist[r1-1+shift] eq 0 then r:=r1; break; end if;
				end if;
			end if;

			if dim2 eq 0 and IsDefined(dimlist,r2+1+shift) then
					if dimlist[r2+1+shift] eq 1 then r:=r2+1; break; end if;
			end if;

			r:=r2;
print"ER6";
		end while;
		
	end if;

else

	r:=r1;

end if;
D0:=D+r*A;
print"ER7";
if IsDefined(ElementList,r+shift) then
	a:=ElementList[r+shift];
else	
	 RRSpace(~D0); 	a:=D0`SRedBasis[1];
end if;
//print"ER8,a",a,Height(D0);

return D0+Divisor(a),-r,a,D0;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Summands(D::Rec)->SeqEnum
{Binary dissction of a divosor}
K:=D`FiniteIdeal`Parent;
Divis,Coeffs:=Support(D);
TheDi:=[];

BinaryCeoffs:=[IntegerToBinary(i):i in Coeffs];

max:=Maximum([#ii:ii in BinaryCeoffs]);
L:=[1..#Coeffs];
H:=[];
for i in [1..max] do

	temp:=Divisor(K!1);
	L:=SetToSequence(Set(L) diff Set(H));
	for j in L do
		
		if IsDefined(BinaryCeoffs[j],i) then
			if Abs(BinaryCeoffs[j,i]) eq 1 then
				temp:=temp-BinaryCeoffs[j,i]*Divisor(Divis[j]);
			end if;
		else
			Append(~H,j);
		end if;
		
	end for;
	if #temp`FactorizationString gt 0 then
	TheDi[i]:=temp;
	end if;
end for;

return TheDi;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic SupportReduction(D::Rec,A::Rec)->Rec
{}
K:=D`FiniteIdeal`Parent;

if Height(D) lt 2*GENUS(K)+1 then return D,0,K!1;end if;

Divis,Coeffs:=Support(D);
if #Divis le 1 then
	return D,0,K!1;
end if;

DD:=Divisor(K!1);
TheRs:=[];
TheAs:=[];

for i in [1..#Coeffs] do
		DD,r,a:=ElementaryReduction(Coeffs[i]*Place(Divis[i])+DD,A);
		//print"supp";DD`FactorizationString;
		TheRs[i]:=r;
		TheAs[i]:=a;

end for;
return DD,-1*&+[TheRs[i]:i in [1..#TheRs]],&*[ TheAs[i]:i in [1..#TheAs]];


end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic HeightReduction(D::Rec,A::Rec:DivisorClass:=false)->Rec
{}
K:=D`FiniteIdeal`Parent;
print" HR1";
if Height(D) lt 2*GENUS(K)+1 then return D,0,K!1;end if;//3*GENUS(K)

//first step reduction
rA_1,rA_2:=Support(A);
rD_1,rD_2:=Support(D);
print" HR2";
Acoeffs_inD:=[];

for i in [1..#rA_1] do
	for j in [1..#rD_1] do	
		if rA_1[i] eq rD_1[j] then
//			print"was is los?",rD_2[j]/rA_2[i];
			Append(~Acoeffs_inD,rD_2[j]/rA_2[i]); break;		
		else
			Append(~Acoeffs_inD,0)	; break;	
		end if;
	end for;
end for;	
r_start:=0;

print" HR3";

if forall{o:o in Acoeffs_inD|o gt 0} then 
	r_start:=Minimum([Floor(i):i in Acoeffs_inD]);
end if;	
print" HR4";
D:=D-r_start*A;
if Height(D) lt 2*GENUS(K)+1 then return D,r_start,K!1;end if;//3*GENUS(K)

TheDi:=Summands(D);	TheA:=[];	TheR:=[];
print" HR5";
r_run:=0;	a_run:=K!1;

for i in [1..#TheDi] do
	if IsDefined(TheDi,i) then
		DD,r,a:=SupportReduction(TheDi[i],A);
		TheDi[i]:=DD;	TheR[i]:=r;		TheA[i]:=a;
	end if;	
end for;
print" HR6";
DD:=TheDi[#TheDi]; a_run:=TheA[#TheA]; r_run:=TheR[#TheR];
print" HR6.1";
for j:=#TheDi-1 to 1 by  -1 do
print" HR6.2";
	if IsDefined(TheDi,j) then
		DD,r,a:=ElementaryReduction(2*DD+TheDi[j],A);
		print" HR6.3";
		r_run:=r+2*r_run+TheR[j];
				print" HR6.3.1";
		if not DivisorClass then		
			a_run:=a*a_run^2*TheA[j];
							print" HR6.3.2";
		else
			a_run := 1;
		end if;					
	else
		DD,r,a:=ElementaryReduction(2*DD,A);
		print" HR6.4";
		r_run:=r+2*r_run;	
				print" HR6.4.1";
		if not DivisorClass then						
			a_run:=a*a_run^2;	
							print" HR6.4.2";
		else
			a_run := 1;
		end if;							
	end if;	
end for;
print" HR7";

return DD,r_run,a_run;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic HeightReduction2(D::Rec,A::Rec)->Rec
{}
K:=D`FiniteIdeal`Parent;
if Height(D) lt 2*GENUS(K)+1 then return D,0,K!1;end if;//3*GENUS(K)

//first step reduction
rA_1,rA_2:=Support(A);
rD_1,rD_2:=Support(D);
Acoeffs_inD:=[];

for i in [1..#rA_1] do

	for j in [1..#rD_1] do
	
	
		if rA_1[i] eq rD_1[j] then
			Append(~Acoeffs_inD,rD_2[i]/rA_2[j]); break;
		
		else
			Append(~Acoeffs_inD,0)	; break;
	
		end if;
	end for;
end for;	
r_start:=0;
if forall{o:o in Acoeffs_inD|o gt 0} then 

	r_start:=Minimum([Floor(i):i in Acoeffs_inD]);

end if;	

/*if forall{o:o in Acoeffs_inD|o lt 0} then 

	r_start:=Minimum([Ceiling(i):i in Acoeffs_inD]);

end if;	
*/

D:=D-r_start*A;
if Height(D) lt 2*GENUS(K)+1 then return D,r_start,K!1;end if;//


TheDi:=Summands(D);	TheRs:=[];	TheAs:=[];

for i in [1..#TheDi] do
	if IsDefined(TheDi,i) then
		DD,r,a:=SupportReduction(TheDi[i],A);
		TheDi[i]:=DD;
		TheRs[i]:=r;
		TheAs[i]:=a;
	else
		TheRs[i]:=0;
		TheAs[i]:=K!1;
	end if;
end for;


if IsDefined(TheDi,1)  then
	DD:=TheDi[1];
	DD,r_run,a_run:=ElementaryReduction(DD,A);
else
	DD:=Divisor(K!1);
	r_run:=0;	a_run:=1;
end if;



for ll in [2..#TheDi] do
	if IsDefined(TheDi,ll) then
		D_run:=TheDi[ll];
		for expo in [1..ll-1] do
			D_run:=2*D_run; 
			D_run,r,a:=ElementaryReduction(D_run,A);
			r_run:=r_run+r;
			a_run:=a*a_run;
		end for;
		DD,r,a:=ElementaryReduction(DD+D_run,A);
		r_run:=r_run+r;	a_run:=a_run*a;
		
	end if;
	

end for;

return DD,r_run+&+TheRs,a_run*&*TheAs;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic RiemannRochSpace(~D::Rec:Reduction:=true)
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

if Reduction eq true then

	RRSpace2(~D);
else

	RRSpace(~D);	
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic GENUS(K::FldFun:AbsIrr:=true)->SeqEnum
{Compute the genus g of a function field K/k and the index gc=[k_0:k], where k_0 is the full constant field.}
t1:=Realtime();
if assigned K`Genus then return Integers()!K`Genus,K`ConstanFieldIndex;end if;

t:=PolynomialRing(ConstantField(K)).1;
n:=Degree(K);
index,DegList:=Index(K);
K_iso:=InfinityRepresentation(K);
Montes(K_iso,t);
DegList:= DegList cat [Degree(i):i in K_iso`PrimeIdeals[t]];
indexlocal:=K_iso`LocalIndex[t];
d:=K`Cf;
Append(~DegList,Integers()!(-indexlocal+Integers()!(d*(n-1)*n/2)-index));
Append(~DegList,n);
gc:=GCD(DegList);
gcold:=gc;
newinf:=-n-indexlocal+Integers()!(d*(n-1)*n/2)-index;
tmpp:=1;
if newinf lt 0 then return 0,gc; end if; 
if newinf eq 0 then return 1,1;end if;




if gc gt 1 and not AbsIrr then 
	if IsFinite(ConstantField(K))	then
		Fp:=GF(Characteristic(ConstantField(K)),Degree(ConstantField(K))*gc);
		Fpt:=RationalFunctionField(Fp);	KxT<x> := PolynomialAlgebra(Fpt);
		tmpp:=Factorization(KxT!DefiningPolynomial(K));
		gc:=#Factorization(KxT!DefiningPolynomial(K));
	else
		gc:=Dimension(Divisor(K!1));
	end if;
else 
	gc:=1;	
end if;

g:=1+(-n-indexlocal+Integers()!(d*(n-1)*n/2)-index)/gc;
K`Genus:=Integers()!g;	K`ConstanFieldIndex:=gc;

return Integers()!g,gc,tmpp;


end intrinsic;
///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////


intrinsic SuccessiveMinima(D::Rec:Reduction:=true)->SeqEnum
{Determines the SuccessiveMinima of the lattice corresponding to the divisor D}

if Reduction eq true then 
	RRSpace2(~D:Reduced:=true);
else
	RRSpace(~D:Reduced:=true);
end if;
return D`SuccessiveMinima;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic ApproximatedSuccessiveMinima(D::Rec:Reduction:=true)->SeqEnum
{Determines the SuccessiveMinima of the lattice corresponding to the divisor D}

if Reduction eq true then 
	RRSpace2(~D);
else
	RRSpace(~D);
end if;
return D`ApproximatedSuccessiveMinima;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic SuccessiveMinima(~D::Rec:Reduction:=true)
{Determines the SuccessiveMinima of the lattice corresponding to the divisor D}

if Reduction eq true then 
	RRSpace2(~D:Reduced:=true);
else
	RRSpace(~D:Reduced:=true);
end if;


end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Truncate(~log)
{}

require Degree(log) gt 1: "argument too short to be truncated";
log:=Vector(Remove(Eltseq(log),Degree(log)));
end intrinsic;



/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic Signature(F::FldFun) -> SeqEnum
{}
signature:=[];
for i in PrimesAtInfinity(F) do
	if i`e eq 1 then
		Append(~signature,[0:j in [1..i`f]]);
	else
		Append(~signature,[-j/i`e:j in [0..i`e-1]]);	
	end if;	
end for;
signature:=&cat signature;
return Sort(signature);
end intrinsic;



/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////



intrinsic DivisorReduction(~D::Rec:DivisorClass:=false) 
{}
check:=false;
F:=D`FiniteIdeal`Parent;
if assigned D`IsPrincipal and not assigned D`r then
	D`r:=0; D`SmallDiv:=Divisor(F!1);
	return;
end if;

if IsReductionOn(F) then 
	check:=true;
	SetReduction(F:On:=false);		
end if;


A:=PoleDivisor(F!BaseField(F).1);
D0,r,a:=HeightReduction(D,A:DivisorClass);
if check then 
	SetReduction(F);	
end if;

D`SmallDiv:=D0;	D`r:=r;	D`a:=F!a;
		
end intrinsic;



/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic SetReduction(F::FldFun:On:=true)
{}

if not assigned F`InfinityRepresentation then

	F`InfinityRepresentation:=InfinityRepresentation(F);
end if;

F`ReductionON:=On;
F`InfinityRepresentation`ReductionON:=On;	


end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic IsReductionOn(F::FldFun)-> BoolElt
{}

if assigned F`ReductionON then

	if F`ReductionON then return true; end if;
	
end if;

return false;

end intrinsic;


/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic CRT(elements::SeqEnum[FldFunElt],ideals::SeqEnum[Rec])->FldFunElt
{
Compute  x congruent  to elements[j] mod ideals[j] for every j.
Integrality of the given elements is not checked!
}


r:=#ideals;
require r eq #elements: "The two lists must have the same length";
if r eq 0 then return 0; end if;
if r eq 1 then return elements[1]; end if;
K:=Parent(elements[1]);
k:=ConstantField(K);
kt:=PolynomialRing(k);
require &and[x in K: x in elements]: "Elements should belong to the same function field";
//require &and[IsIntegralM(x): x in elements]: "Elements should all be integral";
require &and[K eq x`Parent: x in ideals]: "The function field of ideals and elements should be the same";
//require &and[IsIntegral(x): x in ideals]: "Ideals should be all integral";
ids:=[x^1: x in ideals]; // We assure they are IdealRecords
if #Set(elements) eq 1 and elements[1] in k then return elements[1]; end if;
S:=[* *];
PrimePols:={@ @};
total:=0;
for i:=1 to r do
    list:=[Prune(x): x in ids[i]`Factorization];
    total+:=#list;
	for entries in list do
		if not entries in S then 
			Append(~S,entries);
		end if;
	end for;
   // S join:=Set(list);
    PrimePols join:={@ x[1]: x in list @};
end for;
require #S eq total: "Ideals must be pairwise coprime.";
if #PrimePols eq 0 then return 0; end if;
ListMaxExps:=[];
MaxMaxExps:=[];
Allcp:=[];
cps:=0;
for p in PrimePols do
    cp:=[K!0: i in [1..r]];
    nprimes:=#K`PrimeIdeals[p];
    exponents:=[0: i in [1..nprimes]];
    indices:=exponents;
    MaxExps:=[0: i in [1..r]];
    for i in [1..r] do
	list:=[x:x in ids[i]`Factorization| x[1] eq p];
	if #list gt 0 then 
	    MaxExps[i]:=Ceiling(Max([x[3]/K`PrimeIdeals[p,x[2]]`e: x in list]));
	    for x in list do
		exponents[x[2]]:=x[3];
		indices[x[2]]:=i;
	    end for;
	end if;
    end for;
    Append(~ListMaxExps,MaxExps);
    Append(~MaxMaxExps,p^(Max(MaxExps)));
    LocalCRT(~K,p,exponents,~cps);
    for i:=1 to r do
        list:=[cps[k]: k in [1..nprimes]|indices[k] eq i];
	if #list gt 0 then 
	    cp[i]:=&+list; 
	end if;
    end for;
    Append(~Allcp,cp);
end for;
solution:=K!0;
for i:=1 to r do
    ci:=K!0;
    for k in [1..#PrimePols] do
	   zeros:=[kt!0: i in [1..#PrimePols]] ;
	   zeros[k]:=1;
	   list:=MaxMaxExps;
	   list[k]:=PrimePols[k]^ListMaxExps[k,i];
	   ci+:=Allcp[k,i]*CRT(zeros,list);
     end for;
     solution+:=ci*elements[i];
end for;
den:=kt!Denominator(solution);
module:=den*&*MaxMaxExps;
num:=Eltseq(Numerator(solution));
num:=PolynomialRing(kt)![kt!x mod module: x in num];
solution:=Evaluate(num,K.1)/K!den;    
return solution;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic LocalCRT(~K,p,exponents,~Multiplicators: Generators:=false)
{}


nprimes:=#K`PrimeIdeals[p];
ntrees:=#K`TreesIntervals[p];
Pieces:=[K!0: i in [1..nprimes]];
MaxVTC:=[];
N:=0;
piece:=0;
for tree in K`TreesIntervals[p] do
    ValuesToCompensate:=[0: k in [1..#tree]]; 
    for tt in tree do
	if exponents[tt] gt 0 then
	    j:=tt-tree[1]+1;
	    if Generators then
		extraden:=Max([0,-K`PrimeIdeals[p,tt]`LogLG[1]]);
	    else
		extraden:=K`PrimeIdeals[p,tt]`exponent;
	    end if;
	    expsTree:=[exponents[tt]+extraden*K`PrimeIdeals[p,tt]`e:tt in tree];// bad choice of t
	    MultPiece(~K`PrimeIdeals[p,tt],tree,expsTree,~N,~piece);
	    Pieces[tt]:=piece;
	    ValuesToCompensate[j]:=N+extraden;
	end if;
    end for;
Append(~MaxVTC,Max(ValuesToCompensate));
end for;

if ntrees eq 1 then
    Betas:=[K!1];
else   
    Compensations:=[];
    beta:=0;
    for i:=1 to ntrees do
	tree:=K`TreesIntervals[p,i];
	max:=Max([MaxVTC[k]: k in Exclude([1..ntrees],i)]);
	expsTree:=[exponents[tt]+max*K`PrimeIdeals[p,tt]`e: tt in tree];
	CompensateValue(~K,p,tree,expsTree,~beta);
	Append(~Compensations,beta);
    end for;
    universe:=&*Compensations;
    Betas:=[universe/x: x in Compensations];
end if;
Multiplicators:=[K!0: i in [1..nprimes]];

for i:=1 to ntrees do
    for tt in K`TreesIntervals[p,i] do
	if exponents[tt] gt 0 then
	    mult:=Pieces[tt]*Betas[i];
	   		if Generators then
				extraden:=Max([0,-K`PrimeIdeals[p,tt]`LogLG[1]]);
		    else
			extraden:=0;
			MultiplyByInverse(~mult,~K`PrimeIdeals[p,tt],exponents[tt]);
	end if;
// simplification
//print "mult",mult;
	    den:=Parent(p)!Denominator(mult);
	    mx:=Max([Ceiling((exponents[k]+extraden)/K`PrimeIdeals[p,k]`e): k in [1..nprimes]]);
	    module:=den*p^mx;
	    num:=PolynomialRing(Parent(p))!Eltseq(Numerator(mult));
	    mult:=Evaluate(num mod module,K.1)/den;    
	    Multiplicators[tt]:=mult;
//print "simplication",mult;
	end if;
    end for;
end for;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////


intrinsic MultPiece(~P,tree,expsTree,~N,~bp)
{output bp has P-value zero and v_Q(bp) >= expsTree[Q]+extraden*e_Q, for all Q\ne P in the tree}
bp:=P`Parent!1;
if #tree eq 1 then    
    return;
end if;
N:=&+[Numerator(x): x in P`CrossedValues];
p:=P`PolynomialGenerator;
ExcludeP:=Exclude(tree,P`Position);
j:=P`Position-tree[1]+1;
for t in ExcludeP do
    k:=t-tree[1]+1;
    outPt:=Exclude(ExcludeP,t);
    if #outPt eq 0 then
	wPkAllPhis:=0;
    else
	wPkAllPhis:=&+[Denominator(P`Parent`PrimeIdeals[p,l]`CrossedValues[j])*P`Parent`PrimeIdeals[p,l]`CrossedValues[k]: l in outPt];
    end if;
    e:=P`Parent`PrimeIdeals[p,t]`e;
    ord:=#P`Parent`PrimeIdeals[p,t]`Type;
    V:=P`Parent`PrimeIdeals[p,t]`Type[ord]`V;
    CVPk:=P`Parent`PrimeIdeals[p,t]`CrossedValues;
    den:=Denominator(CVPk[j]);
    wPk:=((expsTree[k]/e)+N-wPkAllPhis)/den;
   
    SFL(~P`Parent,~P`Parent`PrimeIdeals[p,t],Ceiling(wPk*e)-V);
   
    M:=Max([1+Floor(Max(CVPk)),Ceiling(wPk)]);
   
    phi:=P`Parent`PrimeIdeals[p,t]`Type[ord]`Phi mod p^M;
    //print"phi,den",phi,den,Parent(Evaluate(P`Parent,phi^den));
    bp*:=Evaluate(phi,P`Parent.1)^den;
end for;
bp*:=P`Parent!p^(-N);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic CompensateValue(~K,p,tree,exponents,~beta)
{tree is an interval [i..j] inside [1..#K`PrimeIdeals[p]] and exponents is a sequence of integers of length #tree.
The output is a power of the greatest common phi-polynomial of the tree, such that v_P >= exponents[P] for all P in the tree}

if &and[x le 0: x in exponents] then
    beta:=K!1;
    return;
end if;
level:=0;
phi:=0;
Values:=0;
GCPhi(~K,p,tree,~level,~phi,~Values);
mx:=Max([exponents[k]/Values[k]: k in [1..#tree]]);
if mx le 1 and #tree eq 1 then
    M:=Ceiling(exponents[1]/K`PrimeIdeals[p,tree[1]]`e);
    beta:=Evaluate(K,phi mod p^M);
else
    beta:=Evaluate(K,phi)^Ceiling(mx);
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic MultiplyByInverse(~alpha,~P,m)
{alpha is divided by an inverse, called x, so that the output is congruent to 1 modulo P^m}
require m gt 0: "the third argument must be positive";
value,redalpha:=PValuation(alpha,P: RED:=true);

require value eq 0: "the first argument is not invertible modulo the second argument";
xnum:=0;
xden:=0;
LocalLift(~P`Type,redalpha^(-1),~xnum,~xden);
p:=P`PolynomialGenerator;
alphaden:=Valuation(Parent(p)!Denominator(alpha),p);
precision:=Max([alphaden,2*P`exponent])+Ceiling(m/P`e);
SFL(~P`Parent,~P,precision*P`e-P`Type[#P`Type]`V);
//Zp:=pAdicRing(p,precision);
//Zpx:=PolynomialRing(Zp);
phi:=P`Type[#P`Type]`Phi mod p^precision;
alphanum:=PolynomialRing(Parent(p))![Parent(p)!i mod p^precision:i in Eltseq(Numerator(alpha))] mod phi;
alphanum,alphaden:=reduce(p,alphanum,alphaden);//:QUO:=false
h:=1;
while h lt m do
    h*:=2;
    lowprecision:=2*P`exponent+Ceiling(h/P`e);
    Inversionloop(p,[*alphanum,alphaden*],~xnum,~xden,phi,lowprecision);
end while;  
alpha*:=Evaluate(PolynomialRing(Parent(p))!xnum,P`Parent.1)/p^xden;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic GCPhi(~K,p,tree,~node,~phi,~Values)
{the output phi is the greatest common phi-polynomial of the tree.
Values is the sequence of all v_P(phi(theta)) for P in the tree.  
node is the level of phi}

i:=0;
node:=#K`PrimeIdeals[p,tree[1]]`Type;
if #tree gt 1 then
    for k in Exclude(tree,tree[1]) do
	IndexOfCoincidence(~K`PrimeIdeals[p,tree[1]]`Type,~K`PrimeIdeals[p,k]`Type,~i);
	if node gt i then
	    node:=i;
	end if;
    end for;
end if;
level:=K`PrimeIdeals[p,tree[1]]`Type[node];
if #level`Refinements eq 0 then
    phi:=level`Phi;
else
    phi:=level`Refinements[1,1];
end if;
Values:=[];
for i in tree do
    leveli:=K`PrimeIdeals[p,i]`Type[node];
    if #leveli`Refinements eq 0 then
	firstslope:=leveli`slope;
    else
	firstslope:=leveli`Refinements[1,2];	
    end if;
Append(~Values,(K`PrimeIdeals[p,i]`e div level`prode)*(level`V+firstslope));
end for;
end intrinsic;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Begin IdealsBasis
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic pBasisTriangular(K::FldFun, p::RngUPolElt : exp:=false, store:=false, random_exponent:=[0, 0])-> SeqEnum, SeqEnum, SeqEnum
    { }

    if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
        Montes(K, p : Basis:=false);
    end if;

    // This allows us to only specify up to the highest indexed prime
    // ideal with non-zero exponent.
    if Type(exp) ne BoolElt then
        if #K`PrimeIdeals[p] gt #exp then
            exp cat:= [ Random(random_exponent[1], random_exponent[2])
                            : i in [#exp+1..#K`PrimeIdeals[p]] ];
        end if;
    end if;

    p_basis, nums, dexp := MaxMin(K, p : exponents:=exp);

    if store eq true then
        K`pBasis[p] := p_basis;
    end if;

    return p_basis, nums, dexp, exp;
end intrinsic; // pBasisTriangular


intrinsic HermiteFormBasis(K::FldFun, p::RngUPolElt, nums::SeqEnum, dexp::SeqEnum : algorithm:="triangular", triangular_input:=false, maximal_order:=false)-> SeqEnum
    { }

    if algorithm eq "triangular" then
        HNF_routine := HermiteFormTriangularSimple;
        //hnf_matrix := HermiteFormTriangularSimple(matrix_red);
    elif algorithm eq "magma" then
        HNF_routine := HermiteForm;
        //hnf_matrix := HermiteForm(matrix_red);
    else
        printf "Error: Unknown HNF algorithm %o.\n", algorithm;
        return [];
    end if;

    n := Degree(K);
    maxexp := Maximum(dexp);
    p_max := p^maxexp;
    O := Parent(p);
    KT := BaseField(K);

    if maximal_order eq true then
        Nums := [ [ (O!Coefficient(nums[i], j) * p^(maxexp-dexp[i])) mod p^(maxexp+1)
                    :  j in [n-1..0 by -1] ]
                        : i in [n..1 by -1] ];
    else
        Nums := [ [ O!Coefficient(nums[i], j) * p^(maxexp-dexp[i])
                    :  j in [n-1..0 by -1] ]
                        : i in [n..1 by -1] ];
    end if;

    A := Matrix(Parent(p), Nums);
    H := HNF_routine(A);

    if triangular_input eq false then
        dens := [ (KT!p)^Valuation(H[i,i],p) : i in [1..n] ];

        for i in [1..n] do
            inv := Modinv(O!(H[i,i]/dens[i]), p_max);

            H[i,i] := dens[i];
            for j in [i+1..n] do
                H[i,j] := H[i,j]*inv mod p_max;
            end for;
        end for;

        H := HNF_routine(H);
    end if;

    p_max := K!p_max;
    hnf_basis := Reverse([ K!Reverse(Eltseq(H[i]))/p_max : i in [1..n] ]);

    return hnf_basis; 
end intrinsic; // HermiteFormBasis

intrinsic HermiteFormBasis(K::FldFun, basis::SeqEnum)-> SeqEnum
    { We assume that the (global) basis is triangular. }

    n := #basis;
    kt := PolynomialRing(ConstantField(K));
    dens := [ Denominator(g) : g in Reverse(basis) ];
    maxden := dens[1];

    int_basis := [ g*maxden : g in Reverse(basis) ];
    A := Matrix(kt, [ Reverse(Eltseq(g*maxden, BaseField(K)))
                        : g in Reverse(basis) ]);

    H := HermiteForm(A);

    hnf_basis := [ K!Reverse(Eltseq(H[i]))/maxden : i in [n..1 by -1] ];

    return hnf_basis;
end intrinsic; // HermiteFormBasis


intrinsic pHermiteBasisMaxMin(K::FldFun, p::RngUPolElt : algorithm:="triangle")-> SeqEnum
    { }

    if not assigned(K`pHermiteBasis) or not IsDefined(K`pHermiteBasis, p) then
        if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
            _, _ := Montes(K, p : Basis:=false);
        end if;

        p_basis, nums, dexp := MaxMin(K, p);

        n := Degree(K);
        Dexp := Reverse(dexp);
        maxexp := Dexp[1];
        Nums := [ [ Coefficient(nums[i], j) * p^(maxexp-dexp[i])
                    :  j in [n-1..0 by -1] ]
                        : i in [n..1 by -1] ];

        if algorithm eq "triangle" then
            matrix_red := Matrix(Nums);
            hnf_matrix := HermiteFormTriangularSimple(matrix_red);
        else
            printf "Error: Unknown HNF algorithm %o.\n", algorithm;
            return [];
        end if;

        hnf_matrix := Matrix([ [hnf_matrix[i,j] / hnf_matrix[i,i]
                                : j in [1..n]]
                                    : i in [1..n] ]);
        K`pHermiteBasis[p] := basisFromMatrix(hnf_matrix, dexp, K, p);
    end if;

    return K`pHermiteBasis[p];
end intrinsic; // pHermiteBasisMaxMin

intrinsic SumTimes(a::SeqEnum, b::SeqEnum)-> SeqEnum
    { }

    if #a gt #b then
        b cat:= [Cputime() - Cputime() : i in [#b+1..#a] ];
    elif #a lt #b then
        a cat:= [Cputime() - Cputime() : i in [#a+1..#b] ];
    end if;

    return [ a[i] + b[i] : i in [1..#a] ];
end intrinsic; // SumTimes

intrinsic SIntegralBasisMaxMin(K::FldFun, primelist::SeqEnum, explist::SeqEnum : noskip:=false)-> SeqEnum
    { Compute a local integral basis for the given set of primes. }

    n := Degree(K);
    kt := Parent(primelist[1]);
    Numlist := [];
    Denlist := [];
    DenCRTlist := [];

    for i in [1..#primelist] do
        p := primelist[i];
        exp := explist[i];

		Montes(K, p);
        if #exp lt #K`PrimeIdeals[p] then
            exp cat:= [ 0 : i in [#exp+1..#K`PrimeIdeals[p]] ];
        end if;

        if K`LocalIndex[p] gt 0  or noskip eq true then
           // times := K`Times;
	     //    ((K`Times := [ ];
           // sfl_count := K`SFLCount;
            p_basis, nums, dexp := pBasisTriangular(K, p : exp:=exp);
            //K`Times := SumTimes(K`Times, times);
            //K`SFLCount +:= sfl_count;

            dens := [ BaseField(K)!p^e : e in dexp ];
            alpha := Maximum([ Ceiling(exp[i]/K`PrimeIdeals[p,i]`e)
                                    : i in [1..#exp] ]);
            dens_crt := [ p^(Maximum(alpha, 0)+Maximum(e+1, 0)) : e in dexp ];

            Append(~Numlist, [ Coefficients(g) : g in nums ]);
            Append(~Denlist, dens);
            Append(~DenCRTlist, dens_crt);
        end if;
    end for;

    nprimes := #Denlist;

    if nprimes eq 0 then
        return [K.1^k: k in [0..n-1]];
    end if;

    tmps := Cputime();
    SBasis := [ K | ];

    for i := 1 to n do
        Dens := [ Denlist[k, i] : k in [1..nprimes] ];
        DensCRT := [ DenCRTlist[k,i] : k in [1..nprimes] ];
        coeffs := [];
        for j := 1 to i-1 do
            Nums := [Numlist[k, i, j] : k in [1..nprimes]];
            Append(~coeffs, CRT(Nums, DensCRT));
        end for;
        coeffs cat:= [0: j in [1..n-#coeffs]];
        Append(~SBasis, (K.1^(i-1)+K!coeffs)/&*Dens);
    end for;
//    Append(~K`Times, Cputime() - tmps);

    return SBasis;
end intrinsic; // SIntegralBasisMaxMin


intrinsic IntegralBasisMaxMin(K::FldNum)->SeqEnum
    { Compute a basis of the maximal order Z_K of K and the discriminant of K. }

    if not assigned K`IntegralBasis then
        if not assigned K`Discriminant then
            K`Discriminant := Discriminant(DefiningPolynomial(K));
        end if;
        d := K`Discriminant;

        if not assigned K`FactorizedDiscriminant then
            printf "Discriminant is a %o bit number, factorising...\n",
                Ceiling(Log(2, Abs(d)));
            primelist := PrimeDivisors(d);

            d_fac := [ [p, Valuation(d, p)] : p in primelist ];
        else
            primelist := [ factor[1] : factor in K`FactorizedDiscriminant ];
            d_fac := [ [p, Valuation(d, p)] : p in primelist ];
        end if;

        empty_exp := [ [] : p in primelist ];
        K`IntegralBasis := SIntegralBasisMaxMin(K, primelist, empty_exp);

        // FIXME: Do I really need to assign this to anything other than
        //        what I already have in d_fac?
        K`FactorizedDiscriminant := [];
        for p in primelist do
            d := d div p^(2*K`LocalIndex[p]);
            Append(~K`FactorizedDiscriminant, [p, Valuation(d, p)]);
        end for;
    end if;

    return K`IntegralBasis;
end intrinsic; // IntegralBasisMaxMin

intrinsic idealBasis(I::Rec)-> SeqEnum
    { }

    K := I`Parent;
    kt := PolynomialRing(ConstantField(K));

    if not assigned I`Factorization then
        Factorization(~I);
    end if;

    if not assigned K`Discriminant then
        K`Discriminant := kt!Discriminant(DefiningPolynomial(K));
    end if;
    d := K`Discriminant;

    if not assigned K`FactorizedDiscriminant then
        printf "Discriminant is a degree %o polynomial, factoring...\n",
                    Degree(d);

        sqfree_factors := SquareFreeFactorization(d);
        sq_d := kt!(d / &*[ f[1] : f in sqfree_factors ]);
        K`FactorizedDiscriminant := Factorization(sq_d);
    end if;

    primelist := [ p : p in { f[1] : f in I`Factorization }
                            join { f[1] : f in K`FactorizedDiscriminant } ];

    exp := [ [] : p in primelist ];
    for f in I`Factorization do
        p_ind := Index(primelist, f[1]);
        if #exp[p_ind] lt f[2] then
            // Make exp[p] long enough to fit P_f[2].
            exp[p_ind] cat:= [ 0 : i in [#exp[p_ind]+1..f[2]] ];
        end if;
        exp[p_ind,f[2]] := f[3];
    end for;

    basis := SIntegralBasisMaxMin(I`Parent, primelist, exp);

    return basis;
end intrinsic; // idealBasis

intrinsic pIdealBasis(K::FldNum, p::RngUPolElt, exp::SeqEnum)-> SeqEnum
    { Returns a p-basis of a fractional ideal constructed from the product
      of the prime ideals P_i lying over p with exponent e_i. }

    if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
        _, _ := Montes(K, p : Basis:=false);
    end if;

    // This allows us to only specify up to the highest indexed prime
    // ideal with non-zero exponent.
    if #K`PrimeIdeals[p] gt #exp then
        exp cat:= [ 0 : i in [#exp+1..#K`PrimeIdeals[p]] ];
    end if;

    basis := MaxMin(K, p : exponents:=exp);

    return basis;
end intrinsic; // pIdealBasis


intrinsic pIdealBasis(I::Rec, p::RngUPolElt)-> SeqEnum
    { Returns a p-basis of a fractional ideal}
	
	K	:=	I`Parent;
    if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
        _, _ := Montes(K, p : Basis:=false);
    end if;
    exp:=[0:i in [1..#K`PrimeIdeals[p]]];
	for i in I`Factorization do
		if i[1] eq p then
			exp[i[2]]:=i[3];
		end if;
	end for;
	
    // This allows us to only specify up to the highest indexed prime
    // ideal with non-zero exponent.
    
    basis := MaxMin(K, p : exponents:=exp);

    return basis;
end intrinsic; // pIdealBasis

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic MaxMinCore(okbasis_values::SeqEnum, modifiers::SeqEnum)-> SeqEnum, SeqEnum, List, List
    { The core of the MaxMin algorithm.
      Input:
        - The $\Q$-value of every element of each Okutsu $\P$-basis for all
          $\P$, $\Q$ in the input set.
        - 
      Output:
        - Indices of final basis elements as product of input bases elements
        - Denominator exponents of each basis element
        - The $\P$-value of each basis element for all input $\P$
        - The required $\P$-value of each Montes approximation to $F_\P$ }

    indices := [ ];
    den_exp := [ExtendedReals()|];
    values := [* *];

    s := #okbasis_values;
    J := [ 1 : i in [1..s] ];
    nps := [ #okbasis_values[i]-1 : i in [1..s] ];
    n := &+[ np : np in nps ];

    approx_values := [* 0 : i in [1..s] *];
    req_approx_values := [* 0 : i in [1..s] *];

    for m := 0 to n do
        S := [ &+[ okbasis_values[k,J[k],i]
                    : k in [1..s] ] - modifiers[i]
                        : i in [1..s] ];
        v, u := Min([ S[i] + approx_values[i] : i in [1..s] ]);

        Append(~den_exp, S[u]);
        Append(~indices, J);
        Append(~values, S);

        // Store the required phi_P values.
        if m lt n then
            for i in [1..s] do
                if approx_values[i] eq Infinity() then
                    o_val := S[i] - okbasis_values[i,J[i],i];
                    req_approx_values[i] := Max(req_approx_values[i],
                                                v - o_val);
                end if;
            end for;
        end if;

        J[u] +:= 1;
        if J[u] gt nps[u] then
            approx_values[u] := Infinity();
        end if;
    end for;

    return indices, den_exp, values, req_approx_values;
end intrinsic; // MaxMinCore


intrinsic MaxMin(K::FldFun, p::RngUPolElt : exponents:=false)-> SeqEnum, SeqEnum, SeqEnum
    { }

    maxmin_time := Cputime();
    s := #K`PrimeIdeals[p];
    ok_frames := calculateOkutsuFramesValues(K`PrimeIdeals[p]);
    bases_indices := [* *];

    nps := [ type`e*type`f : type in K`PrimeIdeals[p] ];
    rs := [ #type`Type : type in K`PrimeIdeals[p] ];

    for i := 1 to s do
        Append(~bases_indices, calculateBasisIndices(K`PrimeIdeals[p,i]));
    end for;
    bases_values := computeBasesValues(bases_indices, ok_frames);

    if Type(exponents) eq BoolElt and exponents eq false then
        modifiers := [ 0 : i in [1..s] ];
        maximal_order := true;
    else
        modifiers := [ exponents[i]/K`PrimeIdeals[p,i]`e : i in [1..s] ];
        maximal_order := false;
    end if;
            

    // Call MaxMin Core.
    indices, den_exp, values, req_approx_values := MaxMinCore(bases_values,
                                                              modifiers);

    sfl_time := Cputime();

    liftMontesApproximations(~K`PrimeIdeals[p], req_approx_values);
    updateOkutsuFrames(~ok_frames, K`PrimeIdeals[p]);

    polmul_time := Cputime();

    if #ok_frames eq 1 then
        basis := computeOkutsuBasis(ok_frames[1]);
    else
        mod_exponents := reductionExponents(den_exp[1..#den_exp-1], modifiers);
        basis := computeLocalBasis(indices, bases_indices, ok_frames,
                                   p^mod_exponents[#mod_exponents]);
    end if;

    // Remove the degree n element so we have a non-extended basis.
    basis := basis[1..#basis-1];
    den_exp := den_exp[1..#den_exp-1];

    reduce_time := Cputime();
    reducepBasis(~basis, den_exp, modifiers, p);

    den_exp := [ Floor(v) : v in den_exp ];

    p_basis := [ (K![ Coefficient(basis[i], j)
                    : j in [0..#basis-1] ])/K!p^den_exp[i]
                        : i in [#basis..1 by -1] ];

/*    K`Times cat:= [ sfl_time - maxmin_time,
                    polmul_time - sfl_time,
                    reduce_time - polmul_time,
                    Cputime() - reduce_time ];*/

    return Reverse(p_basis), basis, den_exp;
end intrinsic; // MaxMin


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic liftMontesApproximations(~types::SeqEnum[Rec], req_phip_vals::List : range:=false)
    { Increase each $\phi_\P$ so that it's $\P$-value is at least that of
      the corresponding entry in `req_phip_vals`. }

    if Type(range) eq BoolElt and range eq false then
        range := [1 ..#types];
    end if;

    for i in [1..#req_phip_vals] do
        ri := range[i];
        V := types[ri]`Type[#types[range[i]]`Type]`V;
        required_slope := (req_phip_vals[i] * types[ri]`e) - V;
        if required_slope ge types[ri]`Type[#types[ri]`Type]`slope then
            last_lvl := types[ri]`Type[#types[ri]`Type];
            h := last_lvl`h - last_lvl`cuttingslope;
            lasth := Ceiling(required_slope) - last_lvl`cuttingslope;
            path := PathOfPrecisions(lasth,h);

            SFL(~types[ri]`Type, Ceiling(required_slope));
            
            if #path gt 0 then
                types[ri]`Parent`SFLCount +:= (#path - 1);
            end if;
        end if;
    end for;

end intrinsic; // liftMontesApproximations


intrinsic calculateOkutsuFramesValues(types)-> List
    { Calculate the primary and secondary values for the phi-polynomials of
      the Okutsu frames for all types. }

    type_levels := [#tt`Type - 1 : tt in types ];

    QQ := RationalField();
    values := [ [ [* -1 : j in [1..#types] *]
                : r in [1..#types[i]`Type] ]
                    : i in [1..#types] ];

    for i := 1 to #types do
        lvlsi := types[i]`Type;

        // Calculate primary values.
        for k := 1 to #lvlsi do
            values[i,k,i] := (lvlsi[k]`V + lvlsi[k]`slope)/lvlsi[k]`prode;
        end for;

        // Calculate cross values.
        for j := 1 to i-1 do
            lvlsj := types[j]`Type;

            indco := IndexOfCoincidence(types[i], types[j]);

            if indco gt 0 then
                refi := Append(lvlsi[indco]`Refinements,
                               [* lvlsi[indco]`Phi, lvlsi[indco]`slope *]);
                refj := Append(lvlsj[indco]`Refinements,
                               [* lvlsj[indco]`Phi, lvlsj[indco]`slope *]);
                length := Min(#refi, #refj);
                k := 2;
                while k le length and refi[k,1] eq refj[k,1] do
                    k +:= 1;
                end while;
                cutting_phi := refi[k-1,1];
                slope_i := refi[k-1,2];
                slope_j := refj[k-1,2];
                min_slope := Min(slope_i, slope_j);

                // Calculate the cross values of each $Phi_{k,\P}$ for
                // $k < $\ell$.
                for k := 1 to indco - 1 do
                    values[i,k,j] := values[i,k,i];
                    values[j,k,i] := values[i,k,i];
                end for;

                // Calculate the cross values of each $Phi_{\ell,\P}$.
                min_val := (lvlsi[indco]`V+min_slope)/lvlsi[indco]`prode;
                if cutting_phi eq lvlsj[indco]`Phi then
                    values[j,indco,i] := (lvlsi[indco]`V + slope_i)/
                                                lvlsi[indco]`prode;
                else
                    values[j,indco,i] := min_val;
                end if;
                if cutting_phi eq lvlsi[indco]`Phi then
                    values[i,indco,j] := (lvlsi[indco]`V + slope_j)/
                                                lvlsi[indco]`prode;
                else
                    values[i,indco,j] := min_val;
                end if;

                min_val /:= Degree(lvlsi[indco]`Phi);
            else
                min_val := 0;
            end if;

            // Calculate the cross values of each $Phi_{k,\P}$ for $k > \ell$.
            for k := indco + 1 to #lvlsi do
                values[i,k,j] := Degree(lvlsi[k]`Phi) * min_val;
            end for;
            for k := indco + 1 to #lvlsj do
                values[j,k,i] := Degree(lvlsj[k]`Phi) * min_val;
            end for;


        end for;
    end for;

    // Include the degree of each element of the Okutsu frame and the index of
    // the phi polinomial along with its values.
    ok_frames := [ [ rec<OkutsuFrameLevel|
                            degree:=Degree(types[i]`Type[k]`Phi),
                            index:=k,
                            values:=values[i,k],
                            polynomial:=types[i]`Type[k]`Phi>
                        : k in [1..#types[i]`Type] ]
                            : i in [1..#types] ];

    // If $\phi_1$ has degree greater than 1, add an extra element for the
    // x required to make okutsu basis elements of degree not congruent with 0
    // mod deg(phi_1).
    x := Parent(types[1]`Type[1]`Phi).1;
    for i in [1..#types] do
        if ok_frames[i,1]`degree gt 1 then
            Insert(~ok_frames[i], 1, rec<OkutsuFrameLevel|
                                            degree:=1,
                                            index:=0,
                                            values:=[* 0 : type in types *],
                                            polynomial:=x>);
        end if;
    end for;

    return ok_frames;
end intrinsic; // calculateOkutsuFramesValues


intrinsic updateOkutsuFrame(~frame::SeqEnum, type::Rec, i::RngIntElt)
    { Update an Okutsu frame after a type has been (single factor) lifted. }

    lvlr := type`Type[#type`Type];
    frame[#frame]`polynomial := lvlr`Phi;
    frame[#frame]`values[i] := (lvlr`V + lvlr`slope)/lvlr`prode;

end intrinsic; // updateOkutsuFrame

intrinsic updateOkutsuFrames(~ok_frames::SeqEnum, types::SeqEnum)
    { }

    for i in [1..#ok_frames] do
        updateOkutsuFrame(~ok_frames[i], types[i], i);
    end for;

end intrinsic; // updateOkutsuFrames

intrinsic computeOkutsuBasis(frame)-> SeqEnum
    { Efficiently computes the Okutsu basis for the given Okutsu frame. This is
      produced by the canonical product of the $\phi$-polynomials from. }

    basis := [ Parent(frame[1]`polynomial)!1 ];
    
    for m := 2 to Degree(frame[#frame]`polynomial)+1 do
        _, ri := Min([ (m-1) mod frame[r]`degree : r in [#frame..1 by -1] ]);
        r := #frame - ri + 1;
        Append(~basis, basis[m - frame[r]`degree] * frame[r]`polynomial);
    end for;

    return basis;
end intrinsic; // computeOkutsuBasis

intrinsic computeBasisValues(t_ind, t_frame)-> SeqEnum
    { Efficiently computes the values of a basis. }

    // Sanity check.
    if #t_frame eq 0 then
        return [ [0] ];
    end if;

    // "Normalise" the degrees so the first is 1.
    for k in [#t_frame..1 by -1]  do
        t_frame[k]`degree := Integers()!(t_frame[k]`degree/t_frame[1]`degree);
    end for;

    if Type(t_frame[1]`values[1]) eq List then
        // This okutsu frame is a composite "terminal" frame.
        values := [ [ [ExtendedReals()| 0 : v in val_group]
                        : val_group in t_frame[1]`values ] ];
        for m := 2 to #t_ind do
            v, u := Max([t_ind[m,i]-t_ind[m-1,i] : i in [1..#t_ind[m]]]);
            prev_vals := [ values[m-t_frame[u]`degree,j]
                                : j in [1..#t_frame[1]`values] ];
            e_vals := [ [ExtendedReals()| prev_vals[j,k]+t_frame[u]`values[j,k]
                            : k in [1..#prev_vals[j]] ]
                                : j in [1..#prev_vals] ];
            Append(~values, e_vals);
        end for;
    else
        // This is a normal Okutsu frame.
        values := [ [ ExtendedReals()| 0 : j in [1..#t_frame[1]`values] ] ];
        for m := 2 to #t_ind do
            v, u := Max([t_ind[m,i]-t_ind[m-1,i] : i in [1..#t_ind[m]]]);
            e_vals := [ExtendedReals()|
                          values[m-t_frame[u]`degree,j] + t_frame[u]`values[j]
                              : j in [1..#t_frame[1]`values] ];
            Append(~values, e_vals);
        end for;
    end if;

    return values;
end intrinsic; // computeBasisValues

intrinsic computeBasesValues(indices, okutsu_frames)-> List
    { Efficiently computes the values of all Oktusu bases. }

    bases_values := [ ];

    for i in [1..#indices] do
        values := computeBasisValues(indices[i], okutsu_frames[i]);
        Append(~bases_values, values);
    end for;

    return bases_values;
end intrinsic; // computeBasesValues

intrinsic calculateBasisIndices(type::Rec: mod_lvl:=0)-> List
    { Calculate the indices that represent basis elements. The 0th indiex is
      the exponent of x (only used if f_0 > 1) then the i-th index is the
      exponent of phi_i,P for the P associated with this type. }

    lvls := type`Type;
    m1 := Degree(type`Type[1]`Phi mod type`PolynomialGenerator);
    pools := [ ];

    if mod_lvl eq 0 then
        if m1 gt 1 then
            pools cat:= [ [0..m1-1] ];
        end if;
        mod_lvl := 1;
    end if;
    pools cat:= [ [0..lvls[r]`e * lvls[r]`f - 1] : r in [mod_lvl..#lvls-1] ];
    pools cat:= [ [0] ];

    indices := itertoolsProduct(pools);
    Append(~indices, [ 0 : r in [1..#indices[1]-1] ] cat [1]);

    return indices;
end intrinsic; // calculateBasisIndices


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

intrinsic computeLocalBasis(lb_indices, bases_indices, frames, pprec)-> List
    { Efficiently compute a local basis given the indices of which element
      from each $\P$-basis is used to make up an element of the final basis.

      Note: We don't need to compute the Okutsu basis for each $\P$ to do this,
            just the Okutsu frame. }

    s := #frames;
    local_basis := [* Parent(frames[1,1]`polynomial)!1 *];
    f_bases := [ AssociativeArray() : i in [1..s] ];

    for m := 2 to #lb_indices do
        _, i := Max([lb_indices[m,j]-lb_indices[m-1,j] : j in [1..s]]);
        
//        printf "%3o: %o %o\n", m, lb_indices[m], bases_indices[i,lb_indices[m,i]];
        u_ind := lb_indices[m,i];
        _, u := Max([bases_indices[i,u_ind,j] - bases_indices[i,u_ind-1,j]
                            : j in [1..#bases_indices[i,u_ind]]]);
        ch_index := frames[i,u]`index;
        ch_deg := frames[i,u]`degree;

        if u eq 1 then
            basis_el := local_basis[m-1] * frames[i,1]`polynomial;
        elif ch_index eq 1 then
            basis_el := local_basis[m-ch_deg] * frames[i,u]`polynomial;
        else
            not_i := [1..i-1] cat [i+1..s];
            if &+[ lb_indices[m,j]-lb_indices[m-ch_deg,j] : j in not_i ] eq 0 then
                basis_el := local_basis[m-ch_deg] * frames[i,u]`polynomial;
            else
                basis_el := 1;
                for i in [1..#bases_indices] do
                    computeOkutsuBasisElement(~f_bases[i], frames[i],
                                              bases_indices[i],
                                              lb_indices[m,i]);
                    basis_el *:=  f_bases[i,lb_indices[m,i]];
                end for;
            end if;
        end if;

        // We reduce each element mod p^prec where prec is the maximum
        // precision required by the basis. This keeps the precision reasonably
        // low.
        basis_el := basis_el mod pprec;
        Append(~local_basis, basis_el);
    end for;


    return [g : g in local_basis];
end intrinsic; // computeLocalBasis

intrinsic computeOkutsuBasisElement(~basis, frame, indices, m)
    { }

    // basis := AssociativeArray();

    if IsDefined(basis, m) then
        return;
    end if;

    if m eq 1 then
        // Cheating a bit, but this *must* be true.
        basis[m] := Parent(frame[1]`polynomial)!1;
    else
        _, u := Max([ indices[m,j]-indices[m-1,j] : j in [1..#indices[m]] ]);
        computeOkutsuBasisElement(~basis, frame, indices,
                                  m - frame[u]`degree);
        basis[m] := basis[m - frame[u]`degree] * frame[u]`polynomial;
    end if;

end intrinsic; // computeOkutsuBasisElement


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic basisFromMatrix(matrix::Mtrx, basis_values, K::FldFun, p::RngUPolElt)->SeqEnum
    { Returns a basis comprised of elements from `K`. }

    n := #basis_values;
    
    return [ K![matrix[i,j] : j in [n..1 by -1]]/p^basis_values[n+1-i] : i in [n..1 by -1] ];
end intrinsic; // basisFromMatrix

intrinsic reductionExponents(dexp::SeqEnum, modifiers::SeqEnum)-> SeqEnum
    { Calculate the exponents for reduction modulo p^nu. }

    max_modifier := Maximum(modifiers);
    mod_exponents := [ Maximum(Ceiling(v + max_modifier), 0)+1 : v in dexp ];

    return mod_exponents;
end intrinsic; // reductionExponents

intrinsic reducepBasis(~nums::SeqEnum, dexp::SeqEnum, modifiers::SeqEnum, p::RngUPolElt)
    { Reduce all basis numerators mod their valuation. }

    // We can reduce each basis element g modulo p^(w_I(g + max))
    max_modifier := Maximum(modifiers);
    mod_exponents := [ Maximum(Ceiling(v + max_modifier), 0)+1 : v in dexp ];
//    printf "\n(reducepBasis) mod_exponents: %o\n", mod_exponents;
    mods := [ p^mod_exponents[1] ];
    prime_cache := AssociativeArray();
    for i in [2..#mod_exponents] do
        delta := mod_exponents[i] - mod_exponents[i-1];
        j := Index(mod_exponents, delta);
        if j gt 0 then
            delta_power := mods[j];
        elif IsDefined(prime_cache, j) then
            delta_power := prime_cache[j];
        else
            delta_power := p^j;
            prime_cache[j] := delta_power;
        end if;
        
        Append(~mods, mods[i-1] * delta_power);
    end for;

    tmps := Cputime();
    n := #nums;
    Ox := Parent(nums[1]);
    for i in [1..n] do
        coeffs := Parent([p]) ! Eltseq(nums[i]);
        nums[i] := Ox ! [ coeffs[j] mod mods[i] : j in [1..#coeffs] ];
    end for;

end intrinsic; // reducepBasis


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//      Utility functions
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic HermiteFormTriangularSimple(A::Mtrx)-> Mtrx
    { Compute the Hermite Normal Form of a square triangular matrix. }

    require Nrows(A) eq Ncols(A): "A must be a square matrix.";
    n := Nrows(A);

    rows_times := [];

    for i in [2..n] do
        for j in [i-1..1 by -1] do
            v := A[j,i] div A[i,i];
            AddRow(~A, -v, i, j);
        end for;
    end for;

    return A; 
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic itertoolsProduct(pools)-> List
    { The ugly implementation of the product function from python's itertools. }

    result := [* [] *];

    for pool in Reverse(pools) do
        midresult := [* *];
        for x in result do
            midresult cat:= [* [ y ] cat x : y in pool *];
        end for;
        result := midresult;
    end for;

    return result;
end intrinsic;




intrinsic pHermiteBasis(K::FldFun,p::RngUPolElt)->SeqEnum
{Compute a  p-integral basis of ZK.}

Montes(K,p: Basis:=true);
if not IsDefined(K`pHermiteBasis,p) then
    n:=Degree(K);
    Nums:=[Reverse(Eltseq(Numerator(xx))): xx in K`pBasis[p]];
    Dens:=[Valuation(Parent(p)!Denominator(xx),p): xx in K`pBasis[p]];
    maxexp:=Max(Dens);
//    Zp:=pAdicRing(p,maxexp+1);
    pi:=p;
   	precision:=maxexp+1;
    Nums:=[[(Parent(p)!Nums[i,j] mod p^precision*pi^(maxexp-Dens[i])) mod p^precision: j in [1..n]]: i in [1..n]];
    H:=HermiteForm(Matrix(Nums));
    Dens:=[p^( maxexp-Valuation(H[i,i],p)): i in [1..n]];
    H:=[[H[i,j] div H[i,i]: j in [1..n]]: i in [1..n]];
    K`pHermiteBasis[p]:=Reverse([K!Reverse(H[k])/Dens[k] : k in [1..n]]);
end if;
return K`pHermiteBasis[p];
end intrinsic;   





intrinsic Full_constant_field(F::FldFun)->FldFin,Map
{Computes Full constant Field (can be done much more efficiently)}

FF := InfinityRepresentation(F); k := ConstantField(F);
A<t> := PolynomialRing(k);
B := pBasisTriangular(FF,t);
dens := [Degree(A!Denominator(i)):i in B];
ind :=1;
found:=exists(ind){ y : y in [1..Degree(F)-1] | y*F`Cf eq dens[y+1]};
if found then
	b := TranslationMap(B[ind+1],F);
	basis := [b^(i):i in [0..Integers()!(Degree(F)/ind)-1]];
else
	basis :=[1];
end if;

m := Integers()!(Degree(F)/ind);
k_0 := ext<k|m>;
map :=hom< k_0-> F | x:->&+[basis[i]*Eltseq(x)[i]:i in [1..m]] >;

return k_0,basis,map;
end intrinsic;   



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Reduction(alpha:: FldFunElt, P:: Rec, m::RngIntElt)->SeqEnum
{reduction map ZK--> ZK/P^m}
require m gt 0: "The third argument should be positive";
beta:=alpha;
Simplify(~beta,~P,m);
value,red:=PValuation(beta,P: RED:=true);
require value ge 0: "First argument should be P-integral";
class:=[P`Type[#P`Type]`Fq!0: i in [1..m]];
while value lt m do
    class[value+1]:=red;
    if value eq m-1 then
	value:=m;
    else	
   
	beta-:=LocalLift(red,P)*P`LocalGenerator^value;
	
	Simplify(~beta,~P,m);
	
	value,red:=PValuation(beta,P: RED:=true);
    end if;
end while;
return class;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
			
intrinsic Simplify(~beta,~P,m)
{beta is P-integral. The output is congruent to beta mod P^m and it has:
denominator=p^power, deg(numerator) less than n_P, and numerator simplified mod p^power+(m/eP)
}

require m gt 0: "the third argument must be positive";
require beta in P`Parent: "function fields of first and second argument do not coincide";
p:=P`PolynomialGenerator;
den,exp,num:=Localize(beta,p);
beta:=P`Parent!0;
precision:=Ceiling(m/P`e)-exp;
if precision gt 0 then
    power:=p^precision;
    SFL(~P`Parent,~P,precision*P`e-P`Type[#P`Type]`V);
    phi:=P`Type[#P`Type]`Phi mod power;
    num:=(InverseMod(den,power)*num mod phi) mod power;
    beta:=Evaluate(num,P`Parent.1)*P`Parent!p^exp;  
end if;
end intrinsic;

///////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
intrinsic PadicDevelopment(alpha::FldFunElt,length::RngIntElt,P::Rec)->SeqEnum
{Berechnet pi entwicklung von v_P(alpha) bis l}

F:=P`Parent;	p:=P`PolynomialGenerator;	K:=BaseField(F);


if alpha in K and P`e eq 1 then
		R,inj:=Completion(K,K!p); R`Precision:=length;
		LL:= Eltseq(inj(alpha));
		if #LL lt length then
			LL:=LL cat [0:i in [1..length-#LL]];
		end if;
		return LL;
else

	n_P:=PValuation(alpha,P);

	if n_P ge 0 then
	
//		if F`Fin eq 0 then
			LL:=Reduction(TranslationMap(alpha,F),P,length+n_P);
//		else	
			LL:=Reduction(alpha,P,length+n_P);
//		end if;	
		return [LL[i]:i in [n_P+1..length+n_P]];
	else

		pi:=P`LocalGenerator;

//		if F`Fin eq 0 then
//			LL:=Reduction(pi^-n_P*TranslationMap(alpha,F),P,length);
//		else	
			LL:=Reduction(pi^-n_P*alpha,P,length);
//		end if;	
		return LL;
	end if;
end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

/*intrinsic TateLichtenbaumPairing(D1::Rec,D2::Rec,m::RngIntElt:DL:=false)->FldFinElt
{Determines the TateLichtenbaumPairing of D1 and D2 w.r.t. m. If DL:=true the output is an element in F_m}

Fq:=ConstantField(D1`FiniteIdeal`Parent);
require IsFinite(Fq): "Routine works only for global function fields";
D2:=Coprime(D1,D2);
DivisorReduction(~D1);
D1s:=m*D1`SmallDiv;
DivisorReduction(~D1s);
D:=m*D1;		D`SmallDiv:=D1s`SmallDiv;	
D`r:=D1`r*m+D1s`r;		D`a:=D1`a^m*D1s`a;
Basis(~D);
require Dimension(D) eq 1 and Degree(D) eq 0: "Third argument times the first one is not a principal divisor";
z:=D`Basis[1];

if DL then
	q:=#Fq;
	gamma:=(q-1)/m;
	require gamma in Integers(): "#F_q is not divisible by m";
	gamma:=Integers()!gamma;
	b:=PrimitiveElement(Fq)^gamma;
	alpha:=z mod D2;
	if IsPrime(m) then
		Fm:=GF(m);
	else
		Fm:=ResidueClassField(m);
	end if;
	return Fm!Log(b,alpha^gamma);

else

	return z mod D2;

end if;
end intrinsic;
*/



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//    Functions to  manipulate ideals
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic TwoElement(I:: Rec)->SeqEnum
{Compute a pair of elements generating the ideal I.}
require IsPrimeIdealRecord(I) or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 
if IsPrimeIdealRecord(I) then return [I`Parent!I`IntegerGenerator, I`Generator]; end if;
if IsZero(I) then return [I`Parent!0,I`Parent!0]; end if;
TwoElement(~I);
return [I`Parent!I`PolynomialGenerator, I`Generator];
end intrinsic;

intrinsic TwoElement(~I:: Rec)
{Compute a pair of elements generating the ideal.}
require IsPrimeIdealRecord(I) or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 

if not IsPrimeIdealRecord(I) then 
    // nothing to do if the ideal is prime; the generator has been already computed
    if not assigned I`Generator then 
        K:=I`Parent;
        R:=PolynomialRing(ConstantField(K));
        I`Generator:=K!0;
        list:=Factorization(I);
        TwoGens:=[];
        Mult:=[];
        pos:=1;
        ig:=1;  // integergenerator
        while pos le #list do 
	       p:=list[pos,1];
	       ppart:=[x: x in list | x[1] eq p];
	       Genp:=K!1;
	       Hp:=0;
	       for P in ppart do
	           index:=P[2];
	           exponent:=P[3];
	           genP:=K`PrimeIdeals[p,index]`LocalGenerator;
	           eP:=K`PrimeIdeals[p,index]`e;
	           Genp*:=genP^exponent;
	           if exponent lt 0 then
	               num:=Eltseq(Numerator(K`PrimeIdeals[p,index]`LocalGenerator));
                   norm:=R!Resultant(PolynomialRing(R)!num,DefiningPolynomial(K));
                   aa:=Valuation(norm,p);
                   res:=norm div p^aa;
	               Genp*:=res^(Abs(exponent));
	           end if;
	           Hp:=Max(Hp, Ceiling(exponent/eP));
	       end for;
	       first:=p^Hp;
	       ig:=ig*first;
	       Append(~TwoGens,[first,Genp]);
	       Append(~Mult,p);   
	       pos:=pos+#ppart;
        end while;
        I`PolynomialGenerator:=R!ig;
        print"hier",Mult;
        if #Mult gt 0 then
	       univ:=(&*Mult)*ig;
	       I`Generator:=&+[TwoGens[j,2]*(univ div (PolynomialRing(ConstantField(K))!TwoGens[j,1] * Mult[j])):j in [1..#Mult]];
	    else 
	    	I`Generator := K!1;   
        end if;
        if not assigned I`Generators then I`Generators:=[K!ig,I`Generator]; end if;
    end if;
end if;    
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic Norm(I::Rec)->RngIntElt
{Compute the norm of the ideal I.}

require IsIdealRecord(I): "Argument is not an IdealRecord record";
require not IsZero(I): "Argument should be a non-zero ideal.";
n:=1;
K:=I`Parent;
for id in Factorization(I) do
    primid:=K`PrimeIdeals[id[1],id[2]];
    n*:=BaseField(K)!id[1]^(id[3]*primid`f);
end for;
return n;
end intrinsic;