with LIST_PACKAGE;
with TEXT_IO; use TEXT_IO;
procedure TOP_SORT is

    package INT_IO is new INTEGER_IO(INTEGER);
    use INT_IO;

    package LIST_PACK is new LIST_PACKAGE(NATURAL);
    use LIST_PACK;

    type PO_ITEM is 
      record
	COUNT : INTEGER := 0;
	SUCC  : LIST := EMPTY_LIST;
      end record;

    type PO_SET is array(NATURAL range <>) of PO_ITEM;

    NO_PRED : LIST := EMPTY_LIST;

    NUM : NATURAL;
    NUM_OUT : INTEGER := 0;

begin

    put_line("Enter the size of the SET:");
    get(NUM);

    declare

	subtype ELEM_RANGE is NATURAL range 1 .. NUM;

	SET : PO_SET(ELEM_RANGE);

	X, Y : ELEM_RANGE;

    begin
	loop
	    begin
		get(X);
		get(Y);

		SET(Y).COUNT := SET(Y).COUNT + 1;

		APPEND(SET(X).SUCC, Y);

	    exception

	 	when END_ERROR => exit;

	    end;
	end loop;

	for I in ELEM_RANGE loop

	    if SET(I).COUNT = 0 then
		APPEND(NO_PRED, I);
	    end if;

	end loop;

	while not IS_EMPTY(NO_PRED) loop

	    REMOVE(NO_PRED, X);

	    put(X);
	    new_line;
	    NUM_OUT := NUM_OUT + 1;

	    while not IS_EMPTY(SET(X).SUCC) loop

		REMOVE(SET(X).SUCC, Y);
		SET(Y).COUNT := SET(Y).COUNT - 1;

		if SET(Y).COUNT = 0 then
		    APPEND(NO_PRED, Y);
		end if;

	    end loop;

	end loop;

    end;

    new_line;
    if NUM = NUM_OUT then
	put_line("The set is topologically sorted");
    else
	put_line("The set is not partially ordered");
    end if;

end TOP_SORT;
