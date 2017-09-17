Attach("+IdealsFF.m");
Attach("Helpfunctions.m");
Attach("Divisor_reduction_with_pre_comp.m");
Fq := GF(13);

A<t> := PolynomialRing(Fq); // polynomial rinc over Fq in t

Ay<y> := PolynomialRing(A);

f := y^2-(t*(t+1)*(t-3)*(t+2)*(t-2));
F<theta> := FunctionField(f);

g := GENUS(F);

B := PoleDivisor(F!t);

initialize_setting(~F,B);// initializing set up


E := RandomDivisor(F,3); // producing a random divisor in free representation

tt_E := New_representation(E); // putting divisor in new representation

// The bolean  variable DivClass is true if we want only represent the class [E] of E otherwise false 

tt_sum := Add_Divisors(tt_E,tt_E:DivClass := true);	// Computing the representation of 2*E

tt_minus := Negative_Operation(tt_E:DivClass := true);  // Computing the representation of -E

tt_ska := Scalar_Multiplication(23,tt_E:DivClass := true); // Computing the representation of 23*E  
