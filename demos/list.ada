generic

    type ELEMENT is private;

package LIST_PACKAGE is

    type LIST is private;

    EMPTY_LIST : constant LIST;

    procedure APPEND(L : in out LIST; E : in ELEMENT);
    procedure REMOVE(L : in out LIST; E : out ELEMENT);
    procedure CONS(E : in ELEMENT; L : in out LIST);

    function  FIRST(L : in LIST) return ELEMENT;
    function  LAST(L : in LIST) return ELEMENT;

    function IS_EMPTY(L : in LIST) return BOOLEAN;

    EMPTY : exception;

private

    type LIST_ITEM;

    type LIST is access LIST_ITEM;

    type LIST_ITEM is
        record
	    ITEM : ELEMENT;
	    LINK : LIST := NULL;
	end record;

    EMPTY_LIST : constant LIST := NULL;

end LIST_PACKAGE;


package body LIST_PACKAGE is

    FREE : LIST := EMPTY_LIST;

    function IS_EMPTY(L : in LIST) return BOOLEAN is
    --
    -- Tests whether the LIST L is empty 
    --
    begin

        return L = EMPTY_LIST;

    end IS_EMPTY;


    function NEW_L(E : in ELEMENT) return LIST is
    --
    -- This procedure creates a list node and places the
    -- element in it.  It uses the FREE list if it is not empty.
    --

	P : LIST;

    begin

	if FREE = EMPTY_LIST then
	    return  new LIST_ITEM'(E, NULL);
	else
	    P := FREE;
	    FREE := FREE.LINK;
	    P.ITEM := E ;
	    return P;
	end if;

    end NEW_L;


    procedure APPEND(L : in out LIST; E : in ELEMENT) is
    --
    -- This procedure appends the element E to the list L.
    --

        P : LIST;

    begin

	P := NEW_L(E);

        if L = EMPTY_LIST then
	    P.LINK := P;
        else
	    P.LINK := L.LINK;
	    L.LINK := P;
        end if;

        L := P;

    end APPEND;


    procedure REMOVE(L : in out LIST; E : out ELEMENT) is
    --
    --  This procedure removes the first item from the list L and
    --  returns its value in E.  
    --  If the list is empty, it raises the exception EMPTY.

        P : LIST;

    begin

        if L = EMPTY_LIST then
	    raise EMPTY;
        end if;

	P := L.LINK;
        E := P.ITEM;

        if P = L then
	    L := NULL;		-- Removed last item from the list
	else
	    L.LINK := P.LINK;
        end if;

	P.LINK := FREE;		-- Add to the free list
	FREE := P;

    end REMOVE;


    procedure CONS(E : in ELEMENT; L : in out LIST) is
    --
    -- This procedure adds the element E onto the front of the list
    --

	P : LIST;

    begin

	if L = EMPTY_LIST then
	    APPEND(L, E);
	else
	    P := L;
	    APPEND(L, E);
	    L := P;
	end if;

    end CONS;


    function  FIRST(L : in LIST) return ELEMENT is
    --
    -- This function returns the first item in the list if the
    -- list is not empty; otherwise it raises the exception EMPTY.
    --
    begin

	if L = EMPTY_LIST then
	    raise EMPTY;
	else
	    return L.LINK.ITEM;
	end if;

    end FIRST;


    function  LAST(L : in LIST) return ELEMENT is
    --
    -- This function returns the last item in the list if the
    -- list is not empty; otherwise it raises the exception EMPTY.
    --
    begin

	if L = EMPTY_LIST then
	    raise EMPTY;
	else
	    return L.ITEM;
	end if;

    end LAST;


end LIST_PACKAGE;
