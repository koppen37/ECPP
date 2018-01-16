//Input: two discriminants
//Output: sorted by ascending classnumber, descending discriminant
DiscriminantSort := function(a,b)
	ca := ClassNumber(a);
	cb := ClassNumber(b);
	if ca eq cb then
		return b - a;
	else
		return ca - cb;
	end if;
end function;

upperbound := 10^6;
primes := PrimesUpTo(upperbound);
discriminants := Sort(SetToSequence({FundamentalDiscriminant(x) : x in [-1..-10^4 by -1]}), func<x,y | DiscriminantSort(x,y) >);

//Check if m can be factored into small primes and probable prime q
//Input: m (the order of an Elliptic Curve E)
//Output: q (the (hopefully) next prime in ECPP)
FactorToQ := function(m)
	for p in primes do
		//Check if remaining is exactly a known prime p
		if p eq m then
			break;
		end if;

		while m mod p eq 0 do
			m div:= p;
		end while;
				
		if p^2 gt m then
			break;
		end if;
	end for;

	return m;
end function;

//Create a random point on a curve with parameters a,b modulo n
//Input: a,b (curve parameters of E in Weiestrass form), n (order of FiniteField on which E is defined)
//Output: Point on E[a,b] mod n
RandomPointOnCurve := function(a,b,n)
	repeat 
		x := Random(0,n-1);
		Q := (Modexp(x,3,n) + a * x + b) mod n;
	until JacobiSymbol(Q, n) ne -1;

	y := Modsqrt(Q,n);
	if Modexp(y,2,n) ne Q then
		"In RandomPointOnCurve: found a divisor of ", n;
	end if;

	return [x,y];
end function;


// Create random point and check if it fullfills the order properties
// Not implemented: check for illegal inversions when performing m*P, (m/q)*P
// Return: Certificate of this round of ECPP
OrderOfPoint := function(E,a,b,m,n,q,D)
	repeat
		P := E ! RandomPointOnCurve(a,b,n);	
		U := (m div q) * P; 
	until U ne E ! 0;

	V := q*U; 
	if U eq E ! 0 then
		"In OrderOfPoint:", n, "is composite";
	end if;

	//Adhere to the magma certificate
	return [* n, Abs(D) , -1, m, [* a, b *], [* IntegerRing() ! P[1], IntegerRing() ! P[2], 1 *], [*[* q, 1 *]*] *];
end function;


// Algorihtm 7.6.2
// Naive implementation of recursive step in ECPP
// Return: certificate for this step (same as OrderOfPoint)
StepNaiveECPP := function(n)
	lb_q := (Root(n,4) + 1)^2;
	sqrt_n := SquareRoot(n);

	repeat
		repeat
		 a := Random(0,n-1);
		 b := Random(0,n-1);
		until GCD(4*a^3 + 27*b^2, n) eq 1;


		E := EllipticCurve([FiniteField(n) | a, b]);
		m := #E;
		q := FactorToQ(m);
	until q gt lb_q and q lt n and IsProbablePrime(q);

	return OrderOfPoint(E,a,b,m,n,q,4*a^3 + 27*b^2 mod n);
end function;

// Algorithm 2.3.13: modified Cornacchia–Smith
// Finds u,v such that: u^2 + |D|v^2 = 4p
// Return: 	u,v as above
//					-1,-1 in case of failure
OrderParameters := function(D,p)
	field := FiniteField(p);

	if p eq 2 then
		if IsSquare(field ! D+8) then
			return Sqrt(D+8),1;
		else
			return -1,-1;
		end if;
	elif JacobiSymbol(D,p) lt 1 then
		return -1, -1;
	end if;

	x := Modsqrt(D,p);
	if (x mod 2 ne D mod 2) then
		x := p - x;
	end if;

	a := 2*p;
	b := x;
	c := Floor(2*Sqrt(p));

	while b gt c do
		tmp := a;
		a := b;
		b := tmp mod b;
	end while;

	t := 4*p-b^2;
	if t mod Abs(D) ne 0 then
		return -1,-1;
	elif not IsSquare(field ! (t div Abs(D))) then
		return -1,-1;
	else
		return IntegerRing() ! Abs(b), IntegerRing() ! Modsqrt(t div Abs(D),p);
	end if;
end function;

// Algorithm 7.5.9
// Find parameters (a,b), given the discriminant D (and the possible orders followed according to this D)
// Return: list of parameters <a,b> that correspond to a order each
CurveParameters := function(D,p)
	//Generate random quadratic (cube) nonresidue
	field := FiniteField(p);
	g := 0;

	if p mod 4 eq 3 then
		g := p - 1;
	elif p mod 8 eq 5 then
		g := 2;
	end if;
		
	i := 1;
	while g eq 0 or IsSquare(field ! g) or (D eq -3 and p mod 3 eq 1 and Modexp(g,(p-1) div 3,p) eq 1) do 
		if i le #primes then
			g := primes[i];
			i +:= 1;
		else 
			g := Random(3,p-1);
		end if;
	end while;

	if D eq -3 then
		return [<0, p - Modexp(g,k,p)>: k in [0..5]];
	elif D eq -4 then
		return [<p - Modexp(g,k,p), 0> : k in [0..3]];
	else 
		T<X> := HilbertClassPolynomial(D);
		S := T mod p;
		j := Roots(S,FiniteField(p))[1][1];
		c := j*(j-1728)^-1;
		r := -3 * c;
		s := 2 * c;
		return [<r,s>, <r*g^2, s*g^3>];
	end if;
end function; 

// Algorithm 7.6.3
// ECPP, where curve is created after finding a suitable m
// Return: certificate for this step (same as OrderOfPoint)
StepECPP := function (n)
	lb_q := (Root(n,4) + 1)^2;

	for d in discriminants do 
		if JacobiSymbol(d,n) ne 1 then
			continue d;
		end if;

		u, v := OrderParameters(d,n);
		if u eq -1 and v eq -1 then
			continue d;
		end if;

		if d eq -3 then
			orders := [n + 1 + u, n + 1 - u, n + 1 + ((u + 3*v) div 2), n + 1 + ((u - 3*v) div 2), n + 1 - ((u + 3*v) div 2), n + 1 - ((u - 3*v) div 2)];
		elif d eq -4 then
			orders := [n + 1 + u, n + 1 - u, n + 1 + 2 * v, n + 1 - 2 * v];
		else
			orders := [n + 1 + u, n + 1 - u];
		end if;

		for o in orders do
			q := FactorToQ(o);

			if q gt lb_q and q lt n and IsProbablePrime(q) then
				params := CurveParameters(d,n);
				D := d; 
				m := o;
				break d;
			end if;
		end for;
	end for;

	for par in params do
		a := IntegerRing() ! par[1];
		b := IntegerRing() ! par[2];
		E := EllipticCurve([FiniteField(n) ! a,b]);

		P := E ! RandomPointOnCurve(a,b,n);
		if m*P eq E ! 0 then
			break;
		end if;
	end for;

	return OrderOfPoint(E,a,b,m,n,q,D);
end function;

//Iteratibly calls StepNaiveECPP/StepECPP 
//Input: n (starting value we want to prove prime), Fast (false: use StepNaiveECPP, true: use StepECPP), Verbose (print number of digits of current prime)
//Output: Prime certificate that can be checked with IsPrimeCertificate function
ECPP := function(n : Fast := true, Verbose := true)
	cert := [* *];
	i := 0;
	repeat
		if Verbose then 
			printf "N_%o: \t %o digits\n", i, Floor(Log(10,n));
		end if;

		if Fast then
			step := StepECPP(n);
		else 
			step := StepNaiveECPP(n);
		end if;
		Append(~cert,step);

		//New value to check
		n := step[7][1][1];
		i +:= 1;
	until n lt upperbound;
	return cert;
end function;

// Run both implementations for value p and print the times
// Should give an impression about the variations in runs and the difference in speed between the implementations
TimeDiff := procedure(p)
	printf "Prime of %o digits: %o\n", Floor(Log(10,p)), p;
	printf "Naive ECPP:\t\t";
	time for i:= 1 to 10 do
		a:= ECPP(p: Fast := false,Verbose := false);
		if IsPrimeCertificate(a) then
			printf ".";
		else
			printf "Something went wrong at %o", i ;
		end if;

		if i eq 10 then 
			printf "\t";
		end if;
	end for;
	
	printf "Less naive ECPP:\t";
	time for i := 1 to 10 do
		a:= ECPP(p: Verbose := false);
		if IsPrimeCertificate(a) then
			printf ".";
		else
			printf "Something went wrong at %o", i ;
		end if;

		if i eq 10 then 
			printf "\t";
		end if;
	end for;

end procedure;

// Run ECPP for 10^a to 10^b with stepsize c
// Also checks that the certificate is indeed valid.
// After running, certs, contains all the certificates
RunFor := procedure(a,b,c,~certs)
	certs := [];

	for i := a to b by c do
		print "\n\ni: ", i;
		"Finding next prime";
		p := NextPrime(10^i);
		time cert := ECPP(p);
		IsPrimeCertificate(cert : ShowCertificate := false, Trust := upperbound);
	end for;
	Append(~certs,cert);
end procedure;