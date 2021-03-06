function curve_line_parser(s : skip_b := true)
    //turns a colon separated file into a list
    //if skip_analyzed is set to false, this will try to parse the b_values,
    //and analyzed points as well,
    //which may fail if their parents are not initialized. the b_values come
    // after the sixth :, so we do not evaluate any field after that.
    curve_data := [**];
    data := "";
    counter := 0;
    for i := 1 to #s do
        if s[i] eq ":" then
	          counter := counter + 1;
	          if skip_b and counter lt 7 then
                Append(~curve_data, eval(data));
            else
                Append(~curve_data, data);
            end if;
            data := "";
        else
            data := data cat s[i];
        end if;
    end for;
    Append(~curve_data, data); // Append final entry of curve_data
    return curve_data;
end function;

function curve_line_parser_bval(s)
    //turns a colon separated file into a list,
    //excluding the last colon separate piece which it returns as a string
    //used for files with bvals because p-adic numbers up to prec cannot be evaluated
    curve_data := [**];
    data := "";
    for i := 1 to #s do
        if s[i] eq ":" then
            Append(~curve_data,eval(data));
            data := "";
        else
            data := data cat s[i];
        end if;
    end for;
    Append(~curve_data,data); // Append final entry of curve_data
    return curve_data;
end function;

function strip(s)
    // Strips s of newline characters
    stripped := "";
    for i := 1 to #s do
        if not s[i] eq "\n" then
            stripped := stripped cat s[i];
        end if;
    end for;
    return stripped;
end function;

procedure curves_divs_parser(curves_path, out_path)
    // Reads in masterrank1wdiv.txt, and writes to
    // outpath in the form disc:f:div. div is taken to
    // either be linear or just the first div in list of
    // divs.
    curves := eval(Read(curves_path));
    parsed_curves := Open(out_path, "a");
    for curve in curves do
        divisors := curve[3];
        divisor := divisors[1];
        for g in divisors do
            if Degree(g) eq 1 then
                divisor := g;
                break;
            end if;
        end for;
        disc := strip(Sprint(curve[1]));
        f := strip(Sprint(curve[2]));
        divisor := strip(Sprint(divisor));
        Puts(parsed_curves, disc cat ":" cat f cat ":" cat divisor);
    end for;
end procedure;
