parameters := AssociativeArray();
parameters["height"] := 1000;
parameters["precision"] := 15;
parameters["precision_inc"] := 5;
parameters["e"] := 40;
parameters["e_inc"] := 20;
parameters["max_e"] := 500;
parameters["max_prec"] := 20;
/*
Computes zeros of vanishing differentials, the candidate rational points.

Inputs - f: quartic f defining curve C: y^3 = f
	   - p: prime at which to do Chabauty-Coleman method
	   - parameters: parameters controling precision and ramification,
	   				 step size, and maximums for these values

outputs - List of (x-coordinates) of candidate points, if successful

Run CC method at prime p with precision N and ramification e, increasing
e to max_e by e_inc (these are stored in parameters) then increasing precision by precision_inc until
max_prec.
*/

function picard_points(f, height)
    P2 := ProjectiveSpace(Rationals(),2);
    C := Curve(P2,Numerator(Evaluate(f,P2.1/P2.3)*P2.3^4-P2.3*P2.2^3));
    points := PointSearch(C, height);
    points := [Coordinates(P) : P in points];
    return points;
end function;


//runs effective chabauty on incrementally larger precision and ramification degrees
//within a box specified by paramters
function effective_chabauty_incremental(f, g, p, parameters)
    prec := parameters["precision"];
    e := parameters["e"];
    precision_inc := parameters["precision_inc"];
    e_inc := parameters["e_inc"];
    finished := false;
    precs := [prec];
    e_vals := [e];
    while e + e_inc le parameters["max_e"] do
        e := e + e_inc;
        Append(~e_vals, e);
    end while;
    while prec + precision_inc le parameters["max_prec"] do
        prec := prec + precision_inc;
        Append(~precs, prec + precision_inc);
    end while;
    for prec in precs do
        data := coleman_data(y^3 - f, p, prec);
        for e in e_vals do
            if Degree(g) eq 1 then
                Qpoints := Q_points(data, parameters["height"]);
                try
                    L,v := effective_chabauty(data:Qpoints:=Qpoints, e:=e);
                    chabauty_data := [*L, Qpoints, p, prec, e*];
                    return true, chabauty_data;
                catch err
                    print(err`Object);
                end try;
            else
                Qpoints := Q_points(data, parameters["height"]); // supp(div(g)) not defined over Q
                Qdivs := Q_divs(data, parameters["height"], g);
                try
                    L,v := effective_chabauty_with_Qdiv(data:Qpoints:=Qdivs, e:=e);
                    chabauty_data := [*L, Qpoints, p, prec, e*];
                    return true, chabauty_data;
                catch err
                    print(err`Object);
                end try;
            end if;
        end for;
    end for;
    return false, [];
end function;



function compare(Qpoints, L)
    // height := cc_parameters["height"];
    // prec := cc_parameters["precision"];
    // e := cc_parameters["e"];
    // data := coleman_data(y^3 - f, p, prec);
    // Qpoints := Q_points(data, height);
    point_coords := [Qpoints[i]`x : i in [1..#Qpoints]];
    candidates := [L[i]`x : i in [1..#L]];
    b_values := [L[i]`b : i in [1..#L]];
    if #point_coords eq #candidates then
        return [], [];
    else
        for xP in point_coords do
            for a in candidates do
                N := Min(Precision(xP),Precision(a));
                if N gt 0 then
                    x_point := ChangePrecision(xP,N);
                    x_cand := ChangePrecision(a,N);
                    if Integers()!x_point eq Integers()!x_cand then
                        idx := Index(candidates, a);
                        Remove(~candidates, idx);
                        Remove(~b_values, idx);
                    end if;
                else
                    if Integers()!xP eq Integers()!a then
                        idx := Index(candidates, a);
                        Remove(~candidates, idx);
                        Remove(~b_values, idx);
                    end if;
                end if;
            end for;
        end for;
        return candidates, b_values;
     end if;
end function;


// Increase precision N and index e until coleman integrals can
// be computed on C: y^3 = f. We integrate from infinity to
// the divisor on C determined by g.

function incremental_tor_test(f, p, g, parameters)
    prec := parameters["precision"];
    e := parameters["e"];
    precision_inc := parameters["precision_inc"];
    e_inc := parameters["e_inc"];
    finished := false;
    precs := [prec];
    e_vals := [e];
    while e + e_inc le parameters["max_e"] do
        e := e + e_inc;
        Append(~e_vals, e);
    end while;
    while prec + precision_inc le parameters["max_prec"] do
        prec := prec + precision_inc;
        Append(~precs, prec + precision_inc);
    end while;
    succcess := false;
    for prec in precs do
        for e in e_vals do
            try
                data := coleman_data(y^3 - f, p, prec);
                is_tor := is_torsion(data, e, g);
                success := true;
                parameters["precision"] := prec;
                parameters["e"] := e;
                return success, is_tor, data, parameters;
            catch err
                print(err`Object);
            end try;
        end for;
    end for;
    return false, true, data, parameters;
end function;

// Finds a non-torsion divisor for C: y^3 = f from div_dict.
// f: degree 4 separable polynomial
// div_dict: associative array with keys = primes p, and
//           div_dict[p] is a list of divisors for C output by
//           RankBounds such that p is coprime to the discriminant of C
//           and if the degree of g is greater than 1, then p splits
//           completely in the splitting field of g.

function find_good_div(f, div_dict)
    primes := Sort([Integers()!p : p in Keys(div_dict)]);
    for p in primes do
        for g in div_dict[p] do
            success, is_tor, data, params := incremental_tor_test(f, p, g, parameters);
            if success and not is_tor then
                return success, p, g, data, params;
            end if;
        end for;
    end for;
    return false, 0, 0, data, params;
end function;

function extras(curve_data, parameters)
    disc := Integers()!curve_data[1];
    f := curve_data[2];  // y^3 = f
    divs := curve_data[3];
    primes := [];
    div_dict := AssociativeArray();
    for g in divs do
        if Degree(g) eq 1 then
            p := 5;
            while disc mod p eq 0 do
                p := NextPrime(p);
            end while;
            if IsDefined(div_dict, p) then
                Append(~div_dict[p], g);
            else
                div_dict[p] := [g];
                Append(~primes, p);
            end if;
        else
            p := first_split_prime(g, disc);
            if IsDefined(div_dict, p) then
                Append(~div_dict[p], g);
            else
                div_dict[p] := [g];
                Append(~primes, p);
            end if;
        end if;
    end for;
    div_success, p, g, data, parameters := find_good_div(f, div_dict);
    if div_success then
        chabauty_success, chabauty_data := effective_chabauty_incremental(f, g, p, parameters);
        if chabauty_success then
            L := chabauty_data[1];
            Qpoints := chabauty_data[2];
            N := chabauty_data[4];
            e := chabauty_data[5];
            extra_zeros, b_values := compare(Qpoints, L);
            extras_data := [];
            for a in extra_zeros do
                Append(~extras_data, [Integers()!a, p, Precision(a)]);
            end for;
            return chabauty_success, g, extras_data, Qpoints, b_values, [p, N, e];
        end if;
    end if;
    return false, 0, [], [], [], [];
end function;

procedure batch_analyze(extras_path,alldata_path,interesting_path,oldfailures_path,newfailures_path:bvals:=false)
    //Analyzes the output from batch_extras using the tests.m patckage
    //takes in paths to various output files, and then sorts the data into files for the user to look at
    //one file contains all data, one contains all "interesting" data of curves with non-WS extra points
    //one file contains old failures from running extras, one file contains bew failures from analyzing
    //new failures should typically come from a failure to run torsion test
    //but in theory could come from points which are not in Chab Coleman set by torsion or linear relations
    //takes in optional argument indicating whether the extras file has bvalues in it, by default false
    curves:=Open(extras_path,"r");
    while true do
        s := Gets(curves);
        if IsEof(s) then
            break;
        else
            alldata_file :=Open(alldata_path,"a");
            interesting_file :=Open(interesting_path,"a");
            oldfailures_file :=Open(oldfailures_path,"a");
            newfailures_file :=Open(newfailures_path,"a");
            if s[1..7] eq "failure" then
                Puts(oldfailures_file,s);
                Puts(alldata_file,s);
            else
                if bvals then
                    curve_data := curve_line_parser_bval(s);
                else
                    curve_data := curve_line_parser(s);
                end if;
                WS :=[];
                Tors :=[* *];
                Relns :=[* *];
                f:=curve_data[2];
                extras:=curve_data[5]; //extra p-adic points found
                failed := false;
                for i in [1 .. #extras] do
                    e:=extras[i];
                    x0:=e[1];
                    deg:=5;
                    height:=100;
                    Qp:=pAdicField(e[2],e[3]);
                    try
                        if ws_test(f,e) then
                            WS:=Append(WS,e);
                        elif torsion_test(f,e,parameters) then //torsion test uses e and max_e parameters
                            tors:=true;
                            search_bnd:=15;
                            order, point, h:=algebraic_test(f, Qp!x0, deg, height, search_bnd, tors: skip_3tor := false);
                            Tors := Append(Tors,e);
                            Tors := Append(Tors,order);
                            Tors := Append(Tors,h);
                        else
                            tors := false;
                            search_bnd:=10;
                            reln, gens, h:= algebraic_test(f,Qp!x0,deg,height,search_bnd, tors: skip_3tor := true);
                            if reln ne [] then
                                Relns := Append(Relns, e);
                                Relns := Append(Relns, reln);
                                Relns := Append(Relns, gens);
                                Relns := Append(Relns, h);
                            else
                                failed := true;
                                Puts(newfailures_file, "failure:" cat s); // failure to explain the point
                                Puts(alldata_file,"failure:" cat s);
                                break i; // don't continue with this curve, otherwise it will print multiple times
                            end if;
                        end if;
                    catch err
                        print err`Object;
                        failed := true;
                        Puts(newfailures_file, "failure:" cat s); //torsion test can fail to compute integrals
                        Puts(alldata_file,"failure:" cat s);
                        break i;
                    end try;
                end for;
                WSpts:=strip(Sprint(WS));
                Torspts:=strip(Sprint(Tors));
                Relnspts := strip(Sprint(Relns));
                if not failed then
                    Puts(alldata_file,s cat ":"cat WSpts cat ":" cat Torspts cat ":" cat Relnspts );
                end if;
                if (#Tors ne 0) or (#Relns ne 0) then
                    Puts(interesting_file,s cat ":"cat WSpts cat ":" cat Torspts cat ":" cat Relnspts );
                end if;
            end if;
        end if;
    end while;
end procedure;

//Batch computes extra points in Chabauty coleman on a list of curves wtih divisors, finds non-torsion divisor

procedure batch_extras(curves_path, extras_path, extras_with_b_path)
    //extras_with_b_path also prints b-values
    curves := Open(curves_path, "r");
    while true do
        s := Gets(curves);
        if IsEof(s) then
            break;
        else
            curve_data := curve_line_parser(s);
            success, g, extras_data, Qpoints, b_values, params := extras(curve_data, parameters);
            extras_file := Open(extras_path, "a");
            extras_with_b_file := Open(extras_with_b_path, "a");
            if success then
                disc := curve_data[1];
                f := curve_data[2];
                curve_data_str := Sprintf("%o:%o:%o", disc, f, g);
                extras_data := strip(Sprint(extras_data));
                b_values := strip(Sprint(b_values));
                params := strip(Sprint(params));
                Qpoints := strip(Sprint(picard_points(f, parameters["height"])));
                Puts(extras_file, curve_data_str cat ":" cat Qpoints cat ":" cat extras_data cat ":" cat params);
                Puts(extras_with_b_file, curve_data_str cat ":" cat Qpoints cat ":" cat extras_data cat ":" cat params cat ":" cat b_values);
            else
                Puts(extras_file, "failure:" cat s);
                Puts(extras_with_b_file, "failure" cat s);
            end if;
            delete(extras_file);
            delete(extras_with_b_file);
        end if;
    end while;
end procedure;
