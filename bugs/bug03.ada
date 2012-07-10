procedure ess is
        x : float := 3.4;
        y : float;
begin
        y := float'large; -- this line is ok
        y := x'large;
end ess;

