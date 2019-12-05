function ws_test(f,extras_data)
    //checks if a point is a weierstrass point by evaluation
    //format of extras_data expected is that given by extras function in experiments.m
    //f is a polynomial defining the picard curve y^3-f

    Qp := pAdicField(extras_data[2],extras_data[3]);
    a := Qp!extras_data[1];
    return IsZero(Evaluate(f,a));
end function;

function torsion_test(f,extras_data, parameters)
    //takes in f defining y^3- f picard curve
    //parameters an associative array with values for e, max_e and e_inc
    //checks whether extras_data is torsion by computing coleman integrals on basis
    //if the integrals are zero up to precision given by extras data, returns true
    //format of extras_data expected is same as output of the extras function in experiments.m

	is_torsion := false;
    p := extras_data[2];
    N := extras_data[3];
    e := parameters["e"];
    data := coleman_data(y^3-f,p,N);
    Qp := pAdicField(p,N);
    infty := set_bad_point(0,[1,0,0],true,data);
    Pt := set_point(Qp!extras_data[1],Root(Evaluate(f,Qp!extras_data[1]),3),data);
    try
    	I := coleman_integrals_on_basis(infty,Pt,data:e:=e);
    	return IsZero(I[1]) and IsZero(I[2]) and IsZero(I[3]);
    catch err
    	if e + parameters["e_inc"] lt parameters["max_e"] then
    		parameters["e"] := parameters["e"] + parameters["e_inc"];
    		is_torsion := torsion_test(f, extras_data, parameters);
        end if;
    end try;
    return is_torsion;
end function;

function torsion_order(f,R,L,search_bnd)
    //simpler version of relation search which searches for the torsion order
    //of a known torsion point. runs much faster for known torsion points
    P2 := ProjectiveSpace(Rationals(),2);
    C := Curve(P2,Numerator(Evaluate(f,P2.1/P2.3)*P2.3^4-P2.3*P2.2^3));
    C := BaseChange(C,L);
    R := Place(C!R);
    infty := Place(C![0,1,0]);
    for i in [1..search_bnd] do
        for j in [1..search_bnd] do
            D := i*R - i*infty;
            if IsPrincipal(D) then
                return i,R;
            end if;
        end for;
    end for;
    return [], [];
end function;


function reln_search(f,R,L,height,search_bnd: skip_3tor := false)
    // Searches in a box for relations on J(Q) involving R
    // R a point on y^3 - f defined over number field L
    // Searches for rational points up to height
    // Iterates over all relations with coefficients abs val most search_bound
    // optional parameter skip_3tor skips 3 torsion points in search
    // setting parameter to true makes search faster
    P2 := ProjectiveSpace(Rationals(),2);
    C := Curve(P2,Numerator(Evaluate(f,P2.1/P2.3)*P2.3^4-P2.3*P2.2^3));
    I := [-search_bnd..search_bnd];
    points := PointSearch(C,height);
    fin_pts := Remove(points,Index(points,C![0,1,0]));
    C := BaseChange(C,L);
    R := Place(C!R);
    fin_pts := [C![P[i] : i in [1..3]] : P in fin_pts];
    infty := Place(C![0,1,0]);
    fin_pts := [Place(P) : P in fin_pts];
    if skip_3tor then
        non_tor := [];
        for P in fin_pts do                 
            if IsPrincipal(3*(P-infty)) then
                continue;
            else
                Append(~non_tor,P);
            end if;
        end for;
        gens := non_tor;
    else
        gens := fin_pts;
    end if;
    comps := [I : i in [1..#gens]];
    Append(~comps,[1..search_bnd]);
    box := CartesianProduct(comps);
    for a in box do
        vector := [a[i] : i in [1..#a]];
        if Gcd(vector) eq 1 then
            D := vector[#vector]*R;
            weight := vector[#vector];
            for i in [1..#vector-1] do
                D := D + vector[i]*gens[i];
                weight := weight + vector[i];
            end for;
            D := D - weight*infty;
            if IsPrincipal(D) then 
                Append(~gens, R);
                return vector, gens;
                break;
            end if;
        end if;
    end for;
    return [], [];
end function;

function algebraic_test(f, x0, d, height, search_bnd, tors: skip_3tor := false)
    // f: quartic defining picard curve C
    // x0: padic zero of Coleman fcn, potential xcoord of
    // an algebraic point of C. Given as a p-adic number.
    // d: degree height for PowerRelation. 5 should suffice?
    // First, we use PowerRelation to find a candidate minimal 
    // poly g for x0. Then we factor h, find an irreducible
    // factor which vanishes at x0, and let 
    // K[a] = K(x) / h(x). We find a root of y^3 - f(a)
    // to get the point R = [a, f(a)^(1/3), 1] on C.
    // We then use reln_search to find relns between R and
    // rational points of C. 
    // ultimately this might not work and it's not proof that your point is not rational
    
    Qp := Parent(x0);
    Qpx := PolynomialRing(Qp);
    g := PowerRelation(x0, d);
    h:=-1;
    for gi in Factorization(g) do
        if IsZero(Evaluate(gi[1], x0)) then
            h := PolynomialRing(Rationals())!gi[1]; //Tries to find a min poly for x0
            break;
        end if;
    end for;
    if h eq -1 then 
        error "x-coordinate not recognizably algebraic"; //If h does not get reassigned, throws an error.
    end if;
    if Degree(h) eq 1 then //if x0 is rational, then we try adjoining a cube root of f(x)
        r:=Roots(h)[1][1];
        K<a> := NumberField(x^3 -Evaluate(f,r));  
        R:=[r,a,1];
    else
        K<a> := NumberField(h); 
        bool, y0 := IsPower(Evaluate(f, a), 3); // this might not be a power, but we don't check for this
        R := [a, y0, 1];
    end if;
    if tors then
        order, point :=torsion_order(f,R,K,search_bnd);
        return order, point, h;
    else 
        reln, gens := reln_search(f, R, K, height, search_bnd:skip_3tor:=skip_3tor);
        return reln, gens, h;
    end if;
end function;