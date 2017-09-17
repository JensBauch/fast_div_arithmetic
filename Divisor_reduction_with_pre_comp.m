// This version does a all the precomputation
Attach("Helpfunctions.m");
Attach("+IdealsFF.m");
// TODO: I have to check that during the initialization the base divisor is not the pole divisor of t. 
//In that case all routines (Add, Pre_Add) have to be updated.
//Attach("~/Mathematik/Programming/Magma/Diss/Helpfunctions/Helpfunctions.m");


AddAttribute(FldFun,"referece_divisor");
AddAttribute(FldFun,"Minus_diff_ideal");
AddAttribute(FldFun,"Minus_diff_basis");
AddAttribute(FldFun,"Different_Divisor");
AddAttribute(FldFun,"Matrix_max_order");
AddAttribute(FldFun,"zero_divisor");
AddAttribute(FldFun,"bases_at_infty");
AddAttribute(FldFun,"basis_in_range");
AddAttribute(FldFun,"basis_in_range_inv");
AddAttribute(FldFun,"B0");

//Record for new divisor representation
				
New_divisor_rep:=recformat<
red_basis: SeqEnum,
succ_min: SeqEnum,
Iinf:Rec,
d: RngIntElt,
k: RngIntElt,
a: FldFunElt,
B_0: Rec
>;





//############################


intrinsic initialize_setting(~F::FldFun,B::Rec)
{}
F`referece_divisor := B;	A := PolynomialRing(ConstantField(F));
Ax := PolynomialRing(A);
F`ReductionON := false;
Minus_diff := -1*Different_Divisor(F);
F`Minus_diff_ideal := Minus_diff`InfiniteIdeal;
F`Minus_diff_basis := SemiReducedBasis(Minus_diff);
F`zero_divisor := New_representation(Divisor(F!1));
F`B0 := PoleDivisor(F!A.1);
//if not B eq F`B0 then
	F`bases_at_infty := [**];
	F`basis_in_range := [];
	for i in [1..Ceiling( (GENUS(F)+Degree(B)-1)/Degree(B))] do
		divi := -i*B;
		RRSpace(~divi);
		tt_minus_iB := rec<New_divisor_rep|red_basis := divi`SRedBasis,	
		succ_min := divi`ApproximatedSuccessiveMinima,
		Iinf := divi`InfiniteIdeal,d := Degree(divi), k := 0,	a := F!1, B_0 := B>;
		Append(~F`basis_in_range,[*-i,tt_minus_iB*]);
	end for;


	F`basis_in_range_inv := [];
	for i in [1..Ceiling( (2*GENUS(F)+Degree(B)-1)/Degree(B))] do
		divi := i*B;
		RRSpace(~divi);
		tt_minus_iB := rec<New_divisor_rep|red_basis := divi`SRedBasis,	
		succ_min := divi`ApproximatedSuccessiveMinima,
		Iinf := divi`InfiniteIdeal,d := Degree(divi), k := 0,	a := F!1, B_0 := B>;
		Append(~F`basis_in_range_inv,[*i,tt_minus_iB*]);
	end for;



//end if;

end intrinsic;


//############################

intrinsic Different_Divisor(F::FldFun)->Rec
{Computes the different divisor of F}

if assigned F`Different_Divisor then 
	return F`Different_Divisor;
end if;

F`Different_Divisor := Complementary_Divisor(Divisor(F!1));
return F`Different_Divisor;


end intrinsic;

//############################


intrinsic Complementary_Divisor(D::Rec)->Rec
{Taking a divisor D, outputs the complementary divisor D^#}



Ifin := D`FiniteIdeal;	Iinf := D`InfiniteIdeal;
F := Ifin`Parent;

if assigned F`Different_Divisor then 
	return F`Different_Divisor-D;
end if;

if not D eq Divisor(F!1) then
	return Different_Divisor(F)-D;
end if;

Ifin_C := Complementary_ideal(Ifin);
Iinf_C := Complementary_ideal(Iinf:Inf := true);

temp1 := SumListToString((Ifin_C^-1)`Factorization,false);
temp2 := SumListToString((Iinf_C^-1)`Factorization,true);

DC := Divisor(F!1);

DC`FiniteIdeal := Ifin_C;	DC`InfiniteIdeal := Iinf_C;	

if #temp1 gt 0 and #temp2 gt 0 then
		DC`FactorizationString:=temp1 cat "+(" cat temp2 cat " )";
	else
		DC`FactorizationString:=temp1 cat temp2;
	end if;

return DC;



end intrinsic;





//############################

intrinsic Complementary_ideal(I::Rec:Inf:=false)->Rec
{Taking a fractional ideal I of the finite maximal order, outputs I^#}

require IsIdealRecord(I): "I has to be an ideal record";
F := I`Parent;
Factorization(~I);
if not Inf then

	I_basis,I_factor:=IdealBase(I);

else
	kt<t> := PolynomialRing(ConstantField(F));
	Montes(F,t);
	I_basis,_,_,_,_,I_exp:=pBasis(I,t);
	I_factor := (F!t)^I_exp;
end if;
I_basis := [b*I_factor: b in I_basis];
M := Matrix(BaseField(F),Degree(F),[Trace(b_i*b_j): b_i in I_basis,b_j in I_basis])^-1;
L := Rows(M);

I_basis_com := [];

for elt in L do

	tmp := &+[elt[i]*I_basis[i]:i in [1..Degree(F)]];
	Append(~I_basis_com,tmp);
end for;

I_C := (ideal(F,I_basis_com))^1;

if Inf then
	Fac := [**];
	for i in I_C`Factorization do	
		if i[1] eq t then
			Append(~Fac,i);
		end if;
	end for;

	I_C`Factorization := Fac; 
	I_C`FactorizationString:=FactorListToString(I_C`Factorization);
end if;

return I_C;

end intrinsic;


/////////////////////////////////////////



intrinsic Count_nonzero_rows(T::ModMatRngElt)->RngIntElt
{}

n := Ncols(T);	m := 0; zero_row := Rows(ZeroMatrix(CoefficientRing(T),1,n))[1];
for i in Rows(T) do

	if not i eq zero_row then 
		m := m+1;
	end if;

end for;
return m;
end intrinsic;

/////////////////////////////////////////

intrinsic Count_nonzero_rows(T::AlgMatElt)->RngIntElt
{}

n := Ncols(T);	m := 0; zero_row := Rows(ZeroMatrix(CoefficientRing(T),1,n))[1];
for i in Rows(T) do

	if not i eq zero_row then 
		m := m+1;
	end if;

end for;
return m;
end intrinsic;

/////////////////////////////////////////



intrinsic ExtendedReductionAlgorithm(T::ModMatRngElt)->AlgMatElt
{Let the rows of T generate a lattice L in K^n, Output: T, whose rows form a reduced basis of L}


NumberRedSteps:=0;
lc := LCM([Denominator(i):i in Eltseq(T)]);
K := BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n := Ncols(T); m := Count_nonzero_rows(T);
m_rank := m;
T := ChangeRing(lc*T,kt);
T_ini := T;
//print"Height of matrix", Max([Degree(T[i,j]):i in [1..Nrows(T)], j in [1..Ncols(T)]]);
s:=1;

if m eq 1 then return T,Maximum([Degree(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p := [];
Sort(~VectorNorm,~p);
T := Matrix([T[i]:i in Eltseq(p)]);
run := 0;
while s lt m_rank do
	
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
		m_rank := Count_nonzero_rows(T);
	end if;
end while;	
//print"NumberRedSteps",NumberRedSteps;
tmp := Rows(T);
Sort(~tmp,~p);
T := Matrix(Reverse(tmp)); VectorNorm := Reverse([VectorNorm[i]:i in  Eltseq(p)]);
tmp := [i-Degree(lc):i in VectorNorm];
return (1/K!lc)*ChangeRing(Submatrix(T,1,1,m_rank,n),K),[tmp[i]: i in [1..m_rank]],NumberRedSteps,T_ini;

end intrinsic;


/////////////////////////////////////////


intrinsic ExtendedReductionAlgorithm(T::AlgMatElt)->AlgMatElt
{Let the rows of T generate a lattice L in K^n, Output: T, whose rows form a reduced basis of L}


NumberRedSteps:=0;
lc := LCM([Denominator(i):i in Eltseq(T)]);
K := BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n := Ncols(T);m := Count_nonzero_rows(T);
m_rank := m;
T := ChangeRing(lc*T,kt);
T_ini := T;
s:=1;

if m eq 1 then return T,Maximum([Degree(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p := [];
Sort(~VectorNorm,~p);
T := Matrix([T[i]:i in Eltseq(p)]);

while s lt m_rank do

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
		m_rank := Count_nonzero_rows(T);
	end if;
end while;	
//print"NumberRedSteps",NumberRedSteps;
tmp := Rows(T);
Sort(~tmp,~p);
T := Matrix(Reverse(tmp)); VectorNorm := Reverse([VectorNorm[i]:i in  Eltseq(p)]);
tmp := [i-Degree(lc):i in VectorNorm];
return (1/K!lc)*ChangeRing(Submatrix(T,1,1,m_rank,n),K),[tmp[i]: i in [1..m_rank]],NumberRedSteps,T_ini;

end intrinsic;

/////////////////////////////////////////

intrinsic Basis_reduction(B::SeqEnum,Iinf::Rec)->SeqEnum
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one}


//if #B le 1 then return B,[1]; end if;
F := Parent(B[1]);	n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;

//////////////////////////Producing bases/////////////////////////
Montes(F2,t);	Binf,_,_,_,_,infex := pBasis(Iinf,t);
Bprime := [TranslationMap(i,F):i in Binf];
M1 := Matrix(K,n,&cat [Eltseq(i):i in B]);
M2 := Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
Mhelp := M2^(-1); T := M1*Mhelp;
RedT,SuccMin,NumberOfRedSteps:=ExtendedReductionAlgorithm(T);
print"NumberOfRedSteps",NumberOfRedSteps;
if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([Degree(j):j in i]):i in RowSequence(T)];
	redbasis:=[i:i in B];
	SuccMin:=[i+infex:i in SuccMin];
	
else	
	redbasis:=[&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..Nrows(RedT)]];
	SuccMin:=[i+infex:i in SuccMin];

end if;

return redbasis,SuccMin;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



intrinsic Basis_reduction(B::SeqEnum,Bprime::SeqEnum,M2::AlgMatElt,infex::RngIntElt)->SeqEnum
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one}

//if #B le 1 then return B,[1]; end if;
F := Parent(B[1]);	n:=Degree(F);
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F));	t:=A.1;
shift:=0;
//////////////////////////Producing bases/////////////////////////
M1 := Matrix(K,n,&cat [Eltseq(i):i in B]);
Mhelp := M2^(-1); T := M1*Mhelp;
RedT,SuccMin,NumberOfRedSteps:=ExtendedReductionAlgorithm(T);
print"NumberOfRedSteps",NumberOfRedSteps;
if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([Degree(j):j in i]):i in RowSequence(T)];
	redbasis:=[i:i in B];
	SuccMin:=[i+infex:i in SuccMin];
	
else	
	redbasis:=[&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..Nrows(RedT)]];
	SuccMin:=[i+infex:i in SuccMin];

end if;

return redbasis,SuccMin;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



intrinsic Basis_reduction_matrix(T::ModMatFldElt,M2_inv::AlgMatElt,infex::RngIntElt,new_row::SeqEnum)->AlgMatElt
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one}


M_tmp := Matrix(#new_row,new_row);
new_row := M_tmp*M2_inv;
T := VerticalJoin(T,new_row);
RedT,SuccMin,NumberOfRedSteps:=ExtendedReductionAlgorithm(T);
print"NumberOfRedSteps",NumberOfRedSteps;
if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([Degree(j):j in i]):i in RowSequence(T)];
	SuccMin:=[i+infex:i in SuccMin];
	
else	
	SuccMin:=[i+infex:i in SuccMin];

end if;

return RedT,SuccMin;
end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Basis_reduction_matrix(T::AlgMatElt,M2_inv::AlgMatElt,infex::RngIntElt,new_row::SeqEnum)->AlgMatElt
{Computes a semi-reduced basis of the lattice corresponding to D and a reduced one}


M_tmp := Matrix(#new_row,new_row);
new_row := M_tmp*M2_inv;
T := VerticalJoin(T,new_row);
RedT,SuccMin,NumberOfRedSteps:=ExtendedReductionAlgorithm(T);
print"NumberOfRedSteps",NumberOfRedSteps;
if NumberOfRedSteps eq 0 then	
	SuccMin := [Maximum([Degree(j):j in i]):i in RowSequence(T)];
	SuccMin:=[i+infex:i in SuccMin];
	
else	
	SuccMin:=[i+infex:i in SuccMin];

end if;

return RedT,SuccMin;
end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////









//////////////////////////////////////////

intrinsic New_representation(E::Rec)->Rec
{Takes a divisor in the free representation and outputs its new representation
	with repsect to a reference divisor B}
//print"E",E`FactorizationString;
require IsDivisor(E): "Argument should be a divisor in free representation";

F := E`FiniteIdeal`Parent;	ref_div := F`referece_divisor;
e := Degree(E);	b := Degree(ref_div);	g := GENUS(F);
k := Floor((-g+e)/b);	tmp:=E-k*ref_div; RRSpace2(~tmp);
_,ind := Minimum(tmp`ApproximatedSuccessiveMinima);	a :=tmp`SRedBasis[ind];

D_eff := E-k*ref_div+Divisor(a);
RRSpace2(~D_eff); succmin := tmp`ApproximatedSuccessiveMinima;

return rec<New_divisor_rep|red_basis := D_eff`SRedBasis,	succ_min := succmin,
	Iinf := D_eff`InfiniteIdeal,d := Degree(D_eff), k := k,	a := a, B_0 := ref_div>,D_eff;

end intrinsic;

//////////////////////////////////////////


intrinsic free_representation(tt_E::Rec)->Rec
{Takes divisor tt_E in new representation and translates it into free one.}

basis := tt_E`red_basis;	F := Parent(basis[1]);  
I := ideal(F,basis);	I_inf:=tt_E`Iinf;
D_eff := Divisor(I)+Divisor(I_inf);

return D_eff+tt_E`k*tt_E`B_0-Divisor(tt_E`a),D_eff;

end intrinsic;

//////////////////////////////////////////


intrinsic check(Iinf::Rec)->SeqEnum
{Checks if basis of Iinf has already been computed.}

FF := Iinf`Parent;	F := FF`InfinityRepresentation;
t := PolynomialRing(ConstantField(F)).1;
ramis := [P`e:P in FF`PrimeIdeals[t]];
expos := [0: i in ramis];
for i in Iinf`Factorization do

	expos[i[2]] := i[3];

end for;
l := 0;
if forall(u){ m : m in expos | m gt 0} or forall(u){ m : m in expos | m lt 0} then
	l := -Sign(expos[1])*Min([(Abs(expos[i])-(Abs(expos[i]) mod ramis[i]))/ramis[i]:i in [1..#ramis]]);
end if;
reduced_expo := [expos[i]+l*ramis[i]:i in [1..#ramis] ];

ind := Position([i[1]:i in F`bases_at_infty],reduced_expo);

if ind eq 0 then

	Binf,_,_,_,_,infex := pBasis(Iinf,t);
	Bprime := [TranslationMap(i,F):i in Binf];
	M2 := Matrix(BaseField(F),Degree(F),&cat [Eltseq(i):i in Bprime]);
	M2_inv := M2^(-1);
	Append(~F`bases_at_infty,[*reduced_expo,M2_inv,Bprime*]);
	
else
	
	M2_inv := F`bases_at_infty[ind,2];
	Bprime := F`bases_at_infty[ind,3];
	infex := -l;	
	
end if;

return M2_inv,infex,Bprime;

end intrinsic;



//////////////////////////////////////////


intrinsic Pre_Add(tt_E::Rec,tt_G::Rec:DivClass := true)-> Rec
{Let D_e and D_g be the effective divisors of tt_E and tt_G. This routine determines
	a reduced basis of D_e+D_g.}


F := Parent(tt_E`red_basis[1]);	F2 := (tt_E`Iinf)`Parent;
d_e := tt_E`d;	d_g := tt_G`d;	b := Degree(F`referece_divisor);	
g := GENUS(F);	n := Degree(F);
Iinf := tt_E`Iinf*tt_G`Iinf;
t := PolynomialRing(ConstantField(F)).1;
Montes(F2,t);	M2_inv,infex,Bprime := check(Iinf);
rhs := -1*(d_e+d_g+1-g-n);	
Basis1 := tt_E`red_basis;
bb := Random(tt_G`red_basis);
Basis2 := Remove(tt_G`red_basis,Position(tt_G`red_basis,bb));
products := []; basis := [bb*b:b in Basis1];	succmin := [rhs-1];
number_of_generators := 0;

M1 := Matrix(BaseField(F),n,&cat [Eltseq(i):i in basis]);
T := M1*M2_inv;
print"T",T;
run := 0;
while not &+succmin eq rhs do
b1 := Random(Basis1);	b2 := Random(Basis2);
		prod := b1*b2;	
		print"where am I?",prod;
		run +:=1; 
		if run gt 100 then
			PutInZ([tt_E,tt_G]);
			print"fail in pre_add";
			print"tt_E,tt_G",tt_E,tt_G;
			return 0;
		end if;
		if not prod in products then
			number_of_generators +:=1;
			Append(~products,prod);
			//Append(~basis,prod);
			new_row := Eltseq(prod);
			print"problem here?";
			T,succmin := Basis_reduction_matrix(T,M2_inv,Integers()!infex,new_row);		
			T := Matrix([T[i]:i in [1..n]]);
			print"check",	&+succmin eq rhs;
			if &+succmin eq rhs then
				print"early exit\n\n";
//				print"needed so many generators :",number_of_generators;
				basis:=[&+[ Bprime[j]*T[i,j] :j in [1..n]]  :i in [1..n]];

				if DivClass then
					a := F!1;	
				else
					a := tt_E`a*tt_G`a;
				end if;
				tt_sum := rec<New_divisor_rep|red_basis := basis, succ_min := succmin, 
								 Iinf := Iinf, d := d_e+d_g, k :=tt_E`k+tt_G`k,	a := a, B_0 := tt_E`B_0>;	
				
				return tt_sum;
			end if;	

		end if;
end while;



print"something is wrong";


return 2;

end intrinsic;

//////////////////////////////////////////


intrinsic infinity_ideal(a::FldFunElt)->Rec
{}
tt := Realtime();
F := Parent(a);
fac := [];
for i in PrimesAtInfinity(F) do
	tmp := PValuation(a,i);
	Append(~fac,i^tmp);
end for;
return &*fac;
end intrinsic;



//////////////////////////////////////////

intrinsic Add_Divisors(tt_E1::Rec,tt_E2::Rec:DivClass := true)->Rec
{Adding two divisors in new representation}
	F := Parent(tt_E1`red_basis[1]);	g := GENUS(F);
	d1 := tt_E1`d;	d2 := tt_E2`d;		B := tt_E1`B_0;
	b := Degree(B);
	
	tt_sum := Pre_Add(tt_E1,tt_E2:DivClass:=DivClass);
	
	if d1 + d2 gt g+b-1 then
		l := Ceiling((d1+d2-(g+b-1))/b);
		if not B eq F`B0 then
		
			pos := Position([i[1]: i in F`basis_in_range],-l);
			minus_l_B := F`basis_in_range[pos,2];
			tt_sum := Pre_Add(tt_sum,minus_l_B);		
		end if;
		
		_,ind := Min(tt_sum`succ_min);
		a := tt_sum`red_basis[ind];	c := a^-1;
		tt_sum`Iinf := tt_sum`Iinf*infinity_ideal(F!c);//*(B`InfiniteIdeal)^-l;
		if F`B0 eq tt_E1`B_0 then
			tt_sum`Iinf := tt_sum`Iinf* (B`InfiniteIdeal)^-l;
		end if;
		tt_sum`red_basis := [c*elt : elt in tt_sum`red_basis];
		tt_sum`d := d1+d2-l*b;	tt_sum`k := tt_E1`k+ tt_E2`k+l;
		if not DivClass then
			tt_sum`a := tt_sum`a*a;
	    end if; 

	end if;

	
	
	
	return tt_sum;	
end intrinsic;

//////////////////////////////////////////



intrinsic Divisor_Inversion(tt_E::Rec:early_exit := false)->SeqEnum
{Takes a divisor tt_E and determines a reduced basis of tt_(-E).}



F := Parent(tt_E`red_basis[1]);
Diff_tt_E_basis := Complementary_basis(tt_E`red_basis);
Diff_tt_E_succ_min := [-i:i in tt_E`succ_min];
Diff := F`Different_Divisor;
tt_Diff_E := rec<New_divisor_rep|red_basis := Diff_tt_E_basis,	 
	Iinf := Diff`InfiniteIdeal*tt_E`Iinf^-1, 	succ_min := Diff_tt_E_succ_min,
		d := Degree(Diff)-tt_E`d, a := F!1, k := 0,	B_0 := tt_E`B_0>;	

tt_minus_Diff := rec<New_divisor_rep|red_basis := F`Minus_diff_basis,  a := F!1, k := 0,	 
	Iinf := Diff`InfiniteIdeal^-1, 	d := -Degree(Diff),	B_0 := tt_E`B_0>;	



t_sum := Pre_Add(tt_Diff_E,tt_minus_Diff);

return t_sum;

end intrinsic;


//////////////////////////////////////////

intrinsic Complementary_basis(basis::SeqEnum)->SeqEnum
{Computes orthogonal basis w.r.t to the trace}
//print"comple_basis_1",basis;
F := Parent(basis[1]); A := PolynomialRing(ConstantField(F));
//basis := [b: b in basis];	
//print"comple_basis_2";
M_temp := Matrix(BaseField(F),Degree(F),[Trace(b_i*b_j): b_i in basis,b_j in basis]);
//print"comple_basis_2.1";
M := M_temp^-1;
//print"comple_basis_3";
L := Rows(M);

basis_com := [];
//print"comple_basis_4";
for elt in L do
	tmp := &+[elt[i]*basis[i]:i in [1..Degree(F)]];
	Append(~basis_com,tmp);
end for;
//print"comple_basis_5";
return basis_com;

end intrinsic;


//////////////////////////////////////////




intrinsic Negative_Operation(tt_E::Rec:DivClass := true)->Rec
{Computes new representation of -E}
	
	F := Parent(tt_E`red_basis[1]);	g := GENUS(F);
	B := tt_E`B_0; b := Degree(B);	d := tt_E`d;	
	l := Ceiling((g+d)/b);
	tt_sum := Divisor_Inversion(tt_E);
	
	
	
	if not B eq F`B0 then
		
		pos := Position([i[1]: i in F`basis_in_range_inv],l);
		l_B := F`basis_in_range_inv[pos,2];
		tt_sum := Pre_Add(tt_sum,l_B);		
	end if;
	
	_,ind := Min(tt_sum`succ_min);	a := tt_sum`red_basis[ind];	c := a^-1;
	red_basis_minus_E := [c*elt : elt in tt_sum`red_basis];
	
	if DivClass then
		fac := F!1;
	else
		fac := tt_E`a^-1*a;
	end if;
	
	/*
	
		
		_,ind := Min(tt_sum`succ_min);
		a := tt_sum`red_basis[ind];	c := a^-1;
		tt_sum`Iinf := tt_sum`Iinf*infinity_ideal(F!c);//*(B`InfiniteIdeal)^-l;
		if F`B0 eq tt_E1`B_0 then
			tt_sum`Iinf := tt_sum`Iinf* (B`InfiniteIdeal)^-l;
		end if;
	
	
	*/
	
	tt_sum`Iinf := tt_E`Iinf^-1*infinity_ideal(F!c);//*(B`InfiniteIdeal)^-l;
	if F`B0 eq tt_E`B_0 then
		tt_sum`Iinf := tt_sum`Iinf* (B`InfiniteIdeal)^-l;
	end if;
	tt_sum`a := fac;
	tt_sum`k := -tt_E`k-l;
	tt_sum`red_basis := red_basis_minus_E;
	
	/*tt_inv := rec<New_divisor_rep|	red_basis := red_basis_minus_E,
		succ_min := sm, k := -tt_E`k-l, d := -d+l*b, a := fac,
			Iinf := tt_E`Iinf^-1*B`InfiniteIdeal^l*infinity_ideal(c), B_0 := tt_E`B_0>;*/
	return tt_sum;	
end intrinsic;


//////////////////////////////////////////


intrinsic Scalar_Multiplication(k::RngIntElt,tt_E::Rec:DivClass := true)->Rec
{Computing k*tt_E}



F := Parent(tt_E`red_basis[1]);
if k eq 0 then return F`zero_divisor; end if;

if k lt 0 then
	tt_E := Negative_Operation(tt_E:DivClass := DivClass);
	k := -k;
end if;

BinaryCeoffs:=IntegerToBinary(k);
_,ind := Max(BinaryCeoffs);		
if ind eq 1 then tt_E_final := tt_E; end if;




for i in [2..#BinaryCeoffs] do
	tt_E := Add_Divisors(tt_E,tt_E:DivClass := DivClass);
	if ind eq i then tt_E_final := tt_E; end if;
	if not ind eq i and not BinaryCeoffs[i] eq 0 then
		tt_E_final := Add_Divisors(tt_E_final,tt_E:DivClass := DivClass);
	end if;
end for;

return tt_E_final;
end intrinsic;


//////////////////////////////////////////////////
//// Routines for Tate-Lichtenbaum Pairing
//////////////////////////////////////////////////


intrinsic finite_ideal(tt_E::Rec)->Rec
{For E=D+rB-(a) this routine computes the finite ideal of D}

Bas := tt_E`red_basis;
F := Parent(Bas[1]); kt := PolynomialRing(ConstantField(F));
dens := [kt!Denominator(b) : b in Bas];
p := 0;
Sort(~dens,~p);
Bas := [Bas[i] : i in Eltseq(p)];
den := dens[#dens];

// has to be improved.... but going from the smaller denominators etc
lcm := LCM(dens);
fac := Factorization(lcm);
if not lcm eq den then print"max deg not lcm"; end if;
Primes := [];
for p in fac do
	Montes(F,p[1]);
	Append(~Primes,F`PrimeIdeals[p[1]]);
end for;
Primes := &cat Primes;
ideal_deg := tt_E`d-Degree(Divisor(tt_E`Iinf));// have to fix degree function for fractional ideals

Min_P_val := [0: i in Primes];
run := 0;
for b in Reverse(Bas) do
	run +:= 1;
	for ind in [1..#Primes] do
		tmp := PValuation(b,Primes[ind]);
		if tmp lt Min_P_val[ind] then
			Min_P_val[ind] := tmp;
		end if;
	end for;
	if -&+[Min_P_val[i]*Degree(Primes[i]):i in [1..#Primes]] eq ideal_deg then 
		print "early exit in finite_ideal", run;
		print"\n";
		return &*[Primes[l]^Min_P_val[l]: l in [1..#Primes]];
	end if;
	
end for;
return 0;
end intrinsic;





