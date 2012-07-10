package u1 is
        type T is private;
    private
        type rep is
            record
                tag : boolean;
                val : integer;
            end record;
        type T is access rep;
    end u1;
